#include "pipeline/tree_unwrapper.h"

#include <slang/parsing/LexerFacts.h>
#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

#include <algorithm>
#include <cstdint>
#include <functional>
#include <gsl/span>
#include <initializer_list>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "data/format_warning.h"
#include "data/unwrapped_line.h"
#include "pipeline/compiler_directives.h"

namespace format {

namespace {

using Token = slang::parsing::Token;
using TK = slang::parsing::TokenKind;
using TriviaKind = slang::parsing::TriviaKind;
using Line = UnwrappedLine<Token>;

struct Production {
  uint16_t left;
  uint16_t offset;
  uint16_t count;
};

#include "annex_a/table.inc"

// The table records token names from the slang revision used by the Annex A
// importer. Resolve names because token enum values differ across revisions.
[[nodiscard]] auto annexTerminal(TK kind) -> int {
  static const auto names = [] {
    std::unordered_map<std::string_view, int> result;
    for (size_t i = 0; i < std::size(kTokenNames); ++i) {
      result.emplace(kTokenNames[i], static_cast<int>(i));
    }
    return result;
  }();
  const auto found = names.find(slang::parsing::toString(kind));
  return found == names.end() ? -1 : found->second;
}

[[nodiscard]] auto annexRule(std::string_view name) -> int {
  static const auto names = [] {
    std::unordered_map<std::string_view, int> result;
    for (size_t i = 0; i < std::size(kRuleNames); ++i) {
      result.emplace(kRuleNames[i], static_cast<int>(i));
    }
    return result;
  }();
  const auto found = names.find(name);
  return found == names.end() ? -1 : found->second;
}

[[nodiscard]] auto annexCanStart(std::string_view name, TK kind) -> bool {
  struct FirstSets {
    std::vector<std::unordered_set<int>> terminals;
    std::vector<bool> nullable;
  };
  static const auto sets = [] {
    FirstSets result{.terminals = std::vector<std::unordered_set<int>>(
                         std::size(kRuleNames)),
                     .nullable = std::vector<bool>(std::size(kRuleNames))};
    bool changed = true;
    while (changed) {
      changed = false;
      for (const auto& production : kProductions) {
        bool all_nullable = true;
        for (size_t i = 0; i < production.count; ++i) {
          const int symbol = kSymbols[production.offset + i];
          if (symbol < 0) {
            changed |=
                result.terminals[production.left].insert(-symbol - 1).second;
            all_nullable = false;
            break;
          }
          for (const int terminal : result.terminals[symbol]) {
            changed |=
                result.terminals[production.left].insert(terminal).second;
          }
          if (!result.nullable[symbol]) {
            all_nullable = false;
            break;
          }
        }
        if (all_nullable && !result.nullable[production.left]) {
          result.nullable[production.left] = true;
          changed = true;
        }
      }
    }
    return result;
  }();
  const int rule = annexRule(name);
  const int terminal = annexTerminal(kind);
  return rule >= 0 && terminal >= 0 &&
         sets.terminals[static_cast<size_t>(rule)].contains(terminal);
}

struct AnnexItem {
  uint16_t production;
  uint16_t dot;
  size_t origin;
  auto operator==(const AnnexItem&) const -> bool = default;
};

struct AnnexItemHash {
  auto operator()(AnnexItem item) const -> size_t {
    size_t hash = item.origin;
    hash ^= static_cast<size_t>(item.production) + 0x9e3779b9U + (hash << 6U) +
            (hash >> 2U);
    hash ^= static_cast<size_t>(item.dot) + 0x9e3779b9U + (hash << 6U) +
            (hash >> 2U);
    return hash;
  }
};

[[nodiscard]] auto annexNext(AnnexItem item) -> int {
  const auto& production = kProductions[item.production];
  return item.dot < production.count ? kSymbols[production.offset + item.dot]
                                     : -32768;
}

// Some Annex A lexical terminals share slang token kinds with other spellings.
// Check slang's source lexeme when the chart scans each such terminal.
[[nodiscard]] auto annexLexemeMatches(AnnexItem item, Token token) -> bool {
  static const int output = annexRule("@lexer_output_symbol");
  static const int level = annexRule("@lexer_level_symbol");
  static const int edge = annexRule("@lexer_edge_symbol");
  static const int edge_descriptor = annexRule("@lexer_edge_descriptor");
  static const int x_digit = annexRule("@lexer_x_digit");
  static const int z_digit = annexRule("@lexer_z_digit");
  static const int binary_number = annexRule("binary_number");
  static const int octal_number = annexRule("octal_number");
  static const int hex_number = annexRule("hex_number");
  const int rule = kProductions[item.production].left;
  const std::string_view lexeme = token.rawText();
  const std::string_view rule_name = kRuleNames[rule];
  const auto matches_base = [&](char lower, char upper) {
    return lexeme.size() >= 2 && lexeme.size() <= 3 && lexeme[0] == '\'' &&
           (lexeme.size() == 2 || lexeme[1] == 's' || lexeme[1] == 'S') &&
           (lexeme.back() == lower || lexeme.back() == upper);
  };
  if (token.kind == TK::IntegerBase) {
    if (rule == binary_number) return matches_base('b', 'B');
    if (rule == octal_number) return matches_base('o', 'O');
    if (rule == hex_number) return matches_base('h', 'H');
    if (rule_name == "@lexer_decimal_number") return matches_base('d', 'D');
  }
  const auto digit_in_base = [&](int base) {
    return !lexeme.empty() && std::ranges::all_of(lexeme, [&](char ch) {
      if (ch == '_' || ch == 'x' || ch == 'X' || ch == 'z' || ch == 'Z' ||
          ch == '?') {
        return true;
      }
      if (ch >= '0' && ch <= '9') return ch - '0' < base;
      return base == 16 &&
             ((ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F'));
    });
  };
  if (rule_name.starts_with("@lexer_binary_value")) {
    return digit_in_base(2) &&
           (rule_name != "@lexer_binary_value" || lexeme.front() != '_');
  }
  if (rule_name.starts_with("@lexer_octal_value")) {
    return digit_in_base(8) &&
           (rule_name != "@lexer_octal_value" || lexeme.front() != '_');
  }
  if (rule_name.starts_with("@lexer_hex_value")) {
    return digit_in_base(16) &&
           (rule_name != "@lexer_hex_value" || lexeme.front() != '_');
  }
  if (rule_name == "@lexer_decimal_number") {
    if (token.kind == TK::IntegerLiteral) {
      return !lexeme.empty() && std::ranges::all_of(lexeme, [](char ch) {
        return ch == '_' || (ch >= '0' && ch <= '9');
      });
    }
    if (token.kind == TK::Identifier) {
      const auto& production = kProductions[item.production];
      const bool after_question =
          item.dot > 0 && kSymbols[production.offset + item.dot - 1] ==
                              -annexTerminal(TK::Question) - 1;
      return !lexeme.empty() &&
             (after_question
                  ? std::ranges::all_of(lexeme,
                                        [](char ch) { return ch == '_'; })
                  : (lexeme[0] == 'x' || lexeme[0] == 'X' || lexeme[0] == 'z' ||
                     lexeme[0] == 'Z') &&
                        std::ranges::all_of(lexeme.substr(1),
                                            [](char ch) { return ch == '_'; }));
    }
  }
  if (rule_name.starts_with('$') && rule_name.ends_with("_timing_check") &&
      item.dot == 0) {
    return lexeme ==
           rule_name.substr(
               0, rule_name.size() - std::string_view("_timing_check").size());
  }
  if (rule == output) {
    return lexeme == "0" || lexeme == "1" || lexeme == "x" || lexeme == "X";
  }
  if (rule == level) {
    return lexeme == "0" || lexeme == "1" || lexeme == "x" || lexeme == "X" ||
           lexeme == "?" || lexeme == "b" || lexeme == "B";
  }
  if (rule == edge) {
    return lexeme == "r" || lexeme == "R" || lexeme == "f" || lexeme == "F" ||
           lexeme == "p" || lexeme == "P" || lexeme == "n" || lexeme == "N" ||
           lexeme == "*";
  }
  if (rule == edge_descriptor) {
    if (kProductions[item.production].count == 2) {
      return item.dot == 0 ? lexeme == "0" || lexeme == "1"
                           : lexeme == "x" || lexeme == "X" || lexeme == "z" ||
                                 lexeme == "Z";
    }
    return lexeme == "01" || lexeme == "10" || lexeme == "x0" ||
           lexeme == "x1" || lexeme == "X0" || lexeme == "X1" ||
           lexeme == "z0" || lexeme == "z1" || lexeme == "Z0" ||
           lexeme == "Z1" || lexeme == "0x" || lexeme == "0X" ||
           lexeme == "1x" || lexeme == "1X" || lexeme == "0z" ||
           lexeme == "0Z" || lexeme == "1z" || lexeme == "1Z";
  }
  if (rule == x_digit) return lexeme == "x" || lexeme == "X";
  if (rule == z_digit) {
    return lexeme == "z" || lexeme == "Z" || lexeme == "?";
  }
  return true;
}

struct AnnexChart {
  size_t position;
  std::vector<AnnexItem> items;
  std::unordered_map<AnnexItem, size_t, AnnexItemHash> index;
  std::unordered_map<int, std::vector<size_t>> waiting;
  std::unordered_map<int, std::vector<size_t>> nullable;
  std::unordered_map<int, std::vector<size_t>> scanning;
  std::unordered_map<int, std::vector<size_t>> completed_origins;
  std::unordered_set<int> completed_roots;

  explicit AnnexChart(size_t position) : position(position) {}

  auto add(AnnexItem item) -> void {
    const size_t offset = items.size();
    if (!index.emplace(item, offset).second) return;
    items.push_back(item);
    const int symbol = annexNext(item);
    if (symbol >= 0) {
      waiting[symbol].push_back(offset);
    } else if (symbol == -32768) {
      const int rule = kProductions[item.production].left;
      completed_origins[rule].push_back(item.origin);
      if (item.origin == position) nullable[rule].push_back(offset);
      if (item.origin == 0) completed_roots.insert(rule);
    } else {
      scanning[-symbol - 1].push_back(offset);
    }
  }
};

// This is temporary state owned by SVParser. The chart advances only when
// SVParser consumes a token; no token span is recognized ahead of formatting.
struct AnnexState {
  struct Checkpoint {
    size_t chart_count;
    size_t total_items;
    bool healthy;
    std::vector<AnnexState> branched_paths;
  };

  std::vector<AnnexChart> charts;
  std::vector<uint16_t> roots;
  size_t total_items = 0;
  bool failed = false;
  bool interrupted = false;
  bool lost_continuation = false;
  std::string_view failure_reason;
  // Conditional compilation can leave several valid Annex A continuations.
  // Each path keeps its own Earley history; the next source token advances all
  // paths in this same parser, without replaying any branch tokens.
  std::vector<AnnexState> alternatives;

  explicit AnnexState(const std::vector<std::string_view>& names) {
    static const auto by_left = [] {
      std::vector<std::vector<uint16_t>> result(std::size(kRuleNames));
      for (size_t i = 0; i < std::size(kProductions); ++i) {
        result[kProductions[i].left].push_back(static_cast<uint16_t>(i));
      }
      return result;
    }();
    charts.emplace_back(0);
    for (const auto name : names) {
      const int rule = annexRule(name);
      if (rule < 0) continue;
      roots.push_back(static_cast<uint16_t>(rule));
      for (const auto production : by_left[static_cast<size_t>(rule)]) {
        charts.back().add({production, 0, 0});
      }
    }
    close();
  }

  auto close() -> void {
    static const auto by_left = [] {
      std::vector<std::vector<uint16_t>> result(std::size(kRuleNames));
      for (size_t i = 0; i < std::size(kProductions); ++i) {
        result[kProductions[i].left].push_back(static_cast<uint16_t>(i));
      }
      return result;
    }();
    static const int binary_operator_rule = annexRule("binary_operator");
    static const int expression_rule = annexRule("expression");
    static const int constant_expression_rule =
        annexRule("constant_expression");
    const size_t position = charts.size() - 1;
    auto& chart = charts.back();
    for (size_t cursor = 0; cursor < chart.items.size(); ++cursor) {
      if (total_items + chart.items.size() > 2000000) {
        failed = true;
        failure_reason = "Annex A ambiguity resource limit";
        return;
      }
      const AnnexItem item = chart.items[cursor];
      const int symbol = annexNext(item);
      if (symbol >= 0) {
        for (const auto child : by_left[static_cast<size_t>(symbol)]) {
          chart.add({child, 0, position});
        }
        if (const auto found = chart.nullable.find(symbol);
            found != chart.nullable.end() && !found->second.empty()) {
          chart.add({item.production, static_cast<uint16_t>(item.dot + 1),
                     item.origin});
        }
      } else if (symbol == -32768) {
        const auto& production = kProductions[item.production];
        const auto& origin = charts[item.origin];
        if (const auto found = origin.waiting.find(production.left);
            found != origin.waiting.end()) {
          const auto parents = found->second;
          // Annex A permits every association of a binary expression chain.
          // All completed left operands admit the same suffix here. Keep the
          // longest left operand for each expression family so an ordinary
          // long chain does not create quadratic chart history.
          const bool binary_operator = production.left == binary_operator_rule;
          size_t longest_expression = position;
          size_t longest_constant_expression = position;
          if (binary_operator) {
            for (const size_t index : parents) {
              const AnnexItem parent = origin.items[index];
              if (parent.dot != 1) continue;
              const int left = kProductions[parent.production].left;
              if (left == expression_rule) {
                longest_expression =
                    std::min(longest_expression, parent.origin);
              } else if (left == constant_expression_rule) {
                longest_constant_expression =
                    std::min(longest_constant_expression, parent.origin);
              }
            }
          }
          for (const size_t index : parents) {
            const AnnexItem parent = origin.items[index];
            if (binary_operator && parent.dot == 1) {
              const int left = kProductions[parent.production].left;
              if ((left == expression_rule &&
                   parent.origin != longest_expression) ||
                  (left == constant_expression_rule &&
                   parent.origin != longest_constant_expression)) {
                continue;
              }
            }
            chart.add({parent.production, static_cast<uint16_t>(parent.dot + 1),
                       parent.origin});
          }
        }
      }
    }
    total_items += chart.items.size();
  }

  [[nodiscard]] auto accepts(TK kind) const -> bool {
    const int terminal = annexTerminal(kind);
    if (terminal < 0 || failed || interrupted) return false;
    if (charts.back().scanning.contains(terminal)) return true;
    return std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return !path.failed && !path.interrupted &&
             path.charts.back().scanning.contains(terminal);
    });
  }

  [[nodiscard]] auto checkpoint() const -> Checkpoint {
    Checkpoint saved{charts.size(), total_items, !failed && !interrupted, {}};
    if (!alternatives.empty()) saved.branched_paths.push_back(*this);
    return saved;
  }

  // An opaque item occupies one grammar nonterminal. Resume the enclosing
  // grammar after that item without treating its unknown tokens as terminals.
  [[nodiscard]] auto skipOpaqueItem(
      Checkpoint saved, const std::vector<uint16_t>& item_roots) -> bool {
    if (!saved.branched_paths.empty()) {
      // Restore every continuation to the point before the unavailable item.
      // A macro may have invalidated some paths while its tokens were read.
      AnnexState restored = std::move(saved.branched_paths.front());
      auto paths = std::move(restored.alternatives);
      restored.alternatives.clear();
      const auto resume = [&](AnnexState& path) {
        return path.skipOpaqueItem(
            {path.charts.size(), path.total_items,
             !path.failed && !path.interrupted, {}},
            item_roots);
      };
      bool valid = resume(restored);
      for (auto& path : paths) {
        valid &= resume(path);
        restored.addContinuation(path);
      }
      *this = std::move(restored);
      if (!valid) interrupted = true;
      return valid;
    }
    if (!saved.healthy || saved.chart_count == 0 ||
        saved.chart_count > charts.size()) {
      return false;
    }
    charts.erase(
        charts.begin() + static_cast<std::ptrdiff_t>(saved.chart_count),
        charts.end());
    total_items = saved.total_items;
    failed = false;
    interrupted = false;
    lost_continuation = false;
    failure_reason = {};
    alternatives.clear();
    AnnexChart next(charts.size());
    const auto& origin = charts.back();
    for (const auto rule : item_roots) {
      if (const auto found = origin.waiting.find(rule);
          found != origin.waiting.end()) {
        for (const auto index : found->second) {
          const AnnexItem parent = origin.items[index];
          next.add({parent.production, static_cast<uint16_t>(parent.dot + 1),
                    parent.origin});
        }
      }
    }
    if (next.items.empty()) {
      interrupted = true;
      return false;
    }
    charts.push_back(std::move(next));
    close();
    return !failed;
  }

  [[nodiscard]] auto sameContinuation(const AnnexState& other) const -> bool {
    if (roots != other.roots || failed != other.failed ||
        interrupted != other.interrupted ||
        lost_continuation != other.lost_continuation) {
      return false;
    }
    if (failed || interrupted) return true;
    // Earley completions consult the origin chart, so equal FIRST sets at the
    // current position do not imply equal continuations. Keep a single chart
    // only when every item and its origin history agree between branches.
    if (charts.size() != other.charts.size()) return false;
    for (size_t i = 0; i < charts.size(); ++i) {
      if (charts[i].items != other.charts[i].items) return false;
    }
    return true;
  }

  auto addContinuation(const AnnexState& other) -> void {
    AnnexState path = other;
    path.alternatives.clear();
    if (!sameContinuation(path) &&
        !std::ranges::any_of(alternatives, [&](const AnnexState& existing) {
          return existing.sameContinuation(path);
        })) {
      alternatives.push_back(std::move(path));
    }
    for (const auto& additional : other.alternatives) {
      addContinuation(additional);
    }
  }

  [[nodiscard]] auto complete() const -> bool {
    if (failed || lost_continuation || charts.size() == 1) return false;
    bool primary_complete = false;
    for (const auto root : roots) {
      primary_complete |= charts.back().completed_roots.contains(root);
    }
    return primary_complete &&
           std::ranges::all_of(alternatives, [](const AnnexState& path) {
             return path.complete();
           });
  }

  [[nodiscard]] auto completed(std::string_view name) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed || lost_continuation || charts.size() == 1) {
      return false;
    }
    return charts.back().completed_roots.contains(rule) &&
           std::ranges::all_of(alternatives, [&](const AnnexState& path) {
             return path.completed(name);
           });
  }

  [[nodiscard]] auto completedFrom(std::string_view name,
                                   size_t origin) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed) return false;
    const auto found = charts.back().completed_origins.find(rule);
    return (found != charts.back().completed_origins.end() &&
            std::find(found->second.begin(), found->second.end(), origin) !=
                found->second.end()) ||
           std::ranges::any_of(alternatives, [&](const AnnexState& path) {
             return path.completedFrom(name, origin);
           });
  }

  [[nodiscard]] auto consumedTerminalInRule(std::string_view name,
                                            TK kind) const -> bool {
    const int rule = annexRule(name);
    const int terminal = annexTerminal(kind);
    if (rule < 0 || terminal < 0 || failed || charts.size() == 1) {
      return false;
    }
    for (const auto item : charts.back().items) {
      const auto& production = kProductions[item.production];
      if (production.left == rule && item.dot > 0 &&
          kSymbols[production.offset + item.dot - 1] == -terminal - 1) {
        return true;
      }
    }
    return std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return path.consumedTerminalInRule(name, kind);
    });
  }

  [[nodiscard]] auto hasViableRule(std::string_view name) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed || charts.empty()) return false;
    return std::ranges::any_of(charts.back().items, [&](AnnexItem item) {
      return item.origin == 0 && kProductions[item.production].left == rule;
    }) || std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return path.hasViableRule(name);
    });
  }

  [[nodiscard]] auto hasActiveRule(std::string_view name) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed || charts.empty()) return false;
    return std::ranges::any_of(charts.back().items, [&](AnnexItem item) {
      return kProductions[item.production].left == rule;
    }) || std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return path.hasActiveRule(name);
    });
  }

  [[nodiscard]] auto hasViableProductionStartingWith(std::string_view name,
                                                     TK kind) const -> bool {
    const int rule = annexRule(name);
    const int terminal = annexTerminal(kind);
    if (rule < 0 || terminal < 0 || failed || charts.empty()) return false;
    return std::ranges::any_of(charts.back().items, [&](AnnexItem item) {
      const auto& production = kProductions[item.production];
      return item.origin == 0 && item.dot > 0 && production.left == rule &&
             production.count > 0 &&
             kSymbols[production.offset] == -terminal - 1;
    }) || std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return path.hasViableProductionStartingWith(name, kind);
    });
  }

  [[nodiscard]] auto expectsRootTerminal(TK kind) const -> bool {
    const int terminal = annexTerminal(kind);
    if (terminal < 0 || failed) return false;
    for (const auto item : charts.back().items) {
      if (item.origin == 0 && annexNext(item) == -terminal - 1 &&
          std::find(roots.begin(), roots.end(),
                    kProductions[item.production].left) != roots.end()) {
        return true;
      }
    }
    return std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return path.expectsRootTerminal(kind);
    });
  }

  auto advance(Token token) -> void {
    if (failed || interrupted) return;
    auto other_paths = std::move(alternatives);
    advanceOne(token);
    for (auto& path : other_paths) path.advanceOne(token);
    lost_continuation |= std::ranges::any_of(
        other_paths, [](const AnnexState& path) {
          return path.failed || path.interrupted || path.lost_continuation;
        });
    std::erase_if(other_paths, [](const AnnexState& path) {
      return path.failed || path.interrupted;
    });
    if (failed && !other_paths.empty()) {
      lost_continuation = true;
      AnnexState first = std::move(other_paths.front());
      other_paths.erase(other_paths.begin());
      *this = std::move(first);
      lost_continuation = true;
    }
    alternatives = std::move(other_paths);
  }

 private:
  auto advanceOne(Token token) -> void {
    if (failed) return;
    const int terminal = annexTerminal(token.kind);
    if (terminal < 0) {
      failed = true;
      failure_reason = "slang token kind outside Annex A inventory";
      return;
    }
    AnnexChart next(charts.size());
    if (const auto found = charts.back().scanning.find(terminal);
        found != charts.back().scanning.end()) {
      for (const size_t index : found->second) {
        const AnnexItem item = charts.back().items[index];
        if (!annexLexemeMatches(item, token)) continue;
        next.add({item.production, static_cast<uint16_t>(item.dot + 1),
                  item.origin});
      }
    }
    if (next.items.empty()) {
      failed = true;
      failure_reason = "tokens do not match Annex A";
      return;
    }
    charts.push_back(std::move(next));
    close();
  }

 public:
};

[[nodiscard]] auto startsWithCompilerDirective(const Line& line) -> bool {
  return !line.tokens.empty() && isCompilerDirective(line.tokens.front());
}

[[nodiscard]] auto isConditionalStartDirective(Token tok) -> bool {
  if (tok.kind != TK::Directive) {
    return false;
  }
  const std::string_view text = tok.rawText();
  return text == "`ifdef" || text == "`ifndef";
}

[[nodiscard]] auto isConditionalAlternativeDirective(Token tok) -> bool {
  if (tok.kind != TK::Directive) {
    return false;
  }
  const std::string_view text = tok.rawText();
  return text == "`else" || text == "`elsif";
}

[[nodiscard]] auto isConditionalEndDirective(Token tok) -> bool {
  return tok.kind == TK::Directive && tok.rawText() == "`endif";
}

[[nodiscard]] auto isConditionalBoundaryDirective(Token tok) -> bool {
  return isConditionalAlternativeDirective(tok) ||
         isConditionalEndDirective(tok);
}

class SVParser {
 public:
  SVParser(gsl::span<const Token> tokens, const FormatStyle& style,
           std::string_view source)
      : tokens_(tokens),
        style_(style),
        source_(source),
        recovery_enabled_(!source.empty()) {}

  auto parse() -> UnwrapResult {
    parseLevel(TK::EndOfFile);
    addLine();
    if (!tokens_.empty() && tokens_.back().kind == TK::EndOfFile) {
      Line eof_line;
      eof_line.tokens.push_back(tokens_.back());
      lines_.push_back(std::move(eof_line));
    }
    return {
        .lines = std::move(lines_),
        .warnings = std::move(warnings_),
    };
  }

 private:
  struct BlockFrame {
    TK close_kind;
    size_t extra_dedent_after_close = 0;
    std::string_view grammar_body;
    bool statement_phase = false;
    bool constructor_body = false;
    bool udp_has_entry = false;
    bool udp_sequential = false;
    bool udp_combinational = false;
    bool udp_nonansi_header = false;
    bool udp_ansi_header = false;
    bool udp_port_on_all_paths = false;
    bool udp_port_on_any_path = false;
    bool udp_initial_seen = false;

    auto operator==(const BlockFrame&) const -> bool = default;
  };

  struct GrammarContext {
    size_t block_depth;
    std::vector<std::string_view> roots;

    auto operator==(const GrammarContext&) const -> bool = default;
  };

  struct ParserState {
    size_t pos = 0;
    Line line;
    size_t indent_level = 0;
    std::vector<BlockFrame> block_stack;
    std::vector<AnnexState> grammar_scopes;
    std::vector<std::optional<AnnexState::Checkpoint>> grammar_checkpoints;
    std::vector<bool> grammar_paused;
    std::vector<bool> grammar_summary_owner;
    std::vector<GrammarContext> grammar_contexts;
  };

  struct BranchResult {
    ParserState state;
    std::vector<Line> lines;
    std::vector<FormatWarning> warnings;
    size_t preserved_source_end = 0;
  };

  struct LeafCheckpoint {
    size_t pos;
    Line line;
    size_t output_size;
    size_t preserved_source_end;
    size_t indent_level;
  };

  struct ListDepth {
    int parens = 0;
    int brackets = 0;
    int braces = 0;

    auto operator==(const ListDepth&) const -> bool = default;
    [[nodiscard]] auto topLevel() const -> bool {
      return parens == 0 && brackets == 0 && braces == 0;
    }
  };

  gsl::span<const Token> tokens_;
  std::reference_wrapper<const FormatStyle> style_;
  std::string_view source_;
  size_t pos_ = 0;
  Line line_;
  std::vector<Line> lines_;
  std::vector<FormatWarning> warnings_;
  size_t preserved_source_end_ = 0;
  size_t indent_level_ = 0;
  std::vector<BlockFrame> block_stack_;
  std::vector<AnnexState> grammar_scopes_;
  std::vector<std::optional<AnnexState::Checkpoint>> grammar_checkpoints_;
  std::vector<bool> grammar_paused_;
  std::vector<bool> grammar_summary_owner_;
  std::vector<GrammarContext> grammar_contexts_;
  size_t last_grammar_warning_pos_ = std::numeric_limits<size_t>::max();
  bool grammar_suspended_ = false;
  bool stop_at_conditional_boundary_ = false;
  bool recovery_enabled_ = true;

  // ---- token access ----

  [[nodiscard]] auto peek(size_t offset = 0) const -> Token {
    size_t idx = pos_ + offset;
    return (idx < tokens_.size()) ? tokens_[idx] : tokens_.back();
  }

  [[nodiscard]] auto at(TK kind, size_t offset = 0) const -> bool {
    return peek(offset).kind == kind;
  }

  auto consume() -> Token {
    if (pos_ >= tokens_.size()) return tokens_.back();
    const Token token = tokens_[pos_];
    if (!grammar_suspended_ && token.kind == TK::Directive &&
        !isCompilerDirective(token)) {
      interruptGrammar("macro expansion unavailable to Annex A");
    }
    if (!grammar_suspended_ && token.kind != TK::Directive) {
      for (size_t i = 0; i < grammar_scopes_.size(); ++i) {
        if (grammar_paused_[i]) continue;
        auto& scope = grammar_scopes_[i];
        if (scope.failed || scope.interrupted) continue;
        if (token.kind == TK::MacroUsage) {
          scope.interrupted = true;
          recordGrammarFallback("macro expansion unavailable to Annex A");
          continue;
        }
        scope.advance(token);
      }
    }
    ++pos_;
    return token;
  }

  auto consumeInto(Line& line) -> void { line.tokens.push_back(consume()); }

  // ---- line management ----

  auto addLine() -> void {
    if (line_.tokens.empty()) {
      return;
    }
    line_.indentation_spaces =
        startsWithCompilerDirective(line_)
            ? 0
            : indent_level_ * style_.get().indentation_spaces;
    lines_.push_back(std::move(line_));
    line_ = Line{};
  }

  // ---- helpers ----

  auto consumeBalancedInto(TK open, TK close, Line& line,
                           TK recovery_close = TK::EndOfFile) -> bool {
    if (!at(open)) return false;
    consumeInto(line);
    ListDepth depth;
    bool valid = true;
    bool diagnosed = false;
    while (pos_ < tokens_.size() && !at(TK::EndOfFile)) {
      if (at(close) && depth.topLevel()) {
        if (!grammarAllows(close)) {
          valid = false;
          if (!diagnosed) {
            recordGrammarFallback("delimited header outside Annex A rule");
            diagnosed = true;
          }
        }
        consumeInto(line);
        if (!valid && !grammar_scopes_.empty() &&
            !grammar_scopes_.back().interrupted) {
          if (!diagnosed) {
            recordGrammarFallback("delimited header outside Annex A rule");
          }
          grammar_scopes_.back().interrupted = true;
        }
        return valid;
      }
      if (recovery_close != TK::EndOfFile &&
          matchesBlockClose(recovery_close, peek().kind)) {
        break;
      }
      if (isConditionalStartDirective(peek()) &&
          !grammar_scopes_.empty()) {
        bool header_ended = true;
        const bool resumed = parseAnnexConditional(
            TK::EndOfFile, header_ended, indent_level_, &depth);
        valid &= resumed;
        diagnosed |= !resumed;
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (at(TK::MacroUsage) ||
          (at(TK::Directive) && !isCompilerDirective(peek()))) {
        // consume() records the precise unavailable-macro fallback.
        consumeInto(line);
        valid = false;
        diagnosed = true;
        continue;
      }
      if (!grammarAllows(peek().kind)) {
        valid = false;
        if (!diagnosed) {
          recordGrammarFallback("delimited header outside Annex A rule");
          diagnosed = true;
        }
        if (!grammar_scopes_.empty()) {
          grammar_scopes_.back().interrupted = true;
        }
      }
      advanceListDepth(depth, peek().kind);
      consumeInto(line);
      if (!grammar_scopes_.empty()) {
        const auto& grammar = grammar_scopes_.back();
        if (grammar.failed) {
          valid = false;
          if (!diagnosed) {
            recordGrammarFallback(grammar.failure_reason);
            diagnosed = true;
          }
        } else if (grammar.interrupted) {
          valid = false;
          diagnosed = true;
        }
      }
    }
    if (!diagnosed) {
      recordGrammarFallback("unterminated Annex A delimited header");
    }
    if (!grammar_scopes_.empty()) grammar_scopes_.back().interrupted = true;
    return false;
  }

  // The grammar scope identifies the closing delimiter of an expression.
  // Delimiter counting is only used after that scope cannot parse the input.
  auto consumeAnnexDelimited(TK open, TK close, std::string_view rule,
                             Line& line) -> void {
    if (!at(open)) return;
    consumeInto(line);
    beginGrammar({rule});
    int depth = 1;
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      const auto& grammar = grammar_scopes_.back();
      if (at(close) && grammar.complete()) {
        static_cast<void>(endGrammar());
        consumeInto(line);
        return;
      }
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_)) {
          break;
        }
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (grammar.failed || grammar.interrupted ||
          !grammar.accepts(peek().kind)) {
        break;
      }
      if (at(open)) ++depth;
      if (at(close)) --depth;
      consumeInto(line);
    }
    recordGrammarFallback("expression outside Annex A rule");
    static_cast<void>(endGrammar());
    // The expression is outside the available grammar stream. Keep its
    // original tokens and stop before the enclosing block if ')' is missing.
    while (!at(TK::EndOfFile) && depth > 0 &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek())) &&
           (block_stack_.empty() ||
            !matchesBlockClose(block_stack_.back().close_kind, peek().kind))) {
      if (at(open)) ++depth;
      if (at(close)) --depth;
      consumeInto(line);
    }
  }

  [[nodiscard]] auto consumeAnnexRule(std::string_view rule,
                                      Line& line) -> bool {
    beginGrammar({rule});
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      const auto& grammar = grammar_scopes_.back();
      if (grammar.complete() && !grammar.accepts(peek().kind)) {
        static_cast<void>(endGrammar());
        return true;
      }
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_)) {
          break;
        }
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (grammar.failed || grammar.interrupted ||
          !grammar.accepts(peek().kind)) {
        break;
      }
      consumeInto(line);
    }
    const bool complete = grammar_scopes_.back().complete();
    static_cast<void>(endGrammar(false));
    if (!complete) recordGrammarFallback("control outside Annex A rule");
    return complete;
  }

  // Parse a grammar subrule up to its enclosing for-header separator.
  // The second stop protects recovery when a separator is missing.
  auto consumeAnnexUntil(TK stop, TK alternate_stop,
                         std::vector<std::string_view> grammar_rules,
                         Line& line) -> bool {
    beginGrammar(std::move(grammar_rules));
    int parens = 0;
    int brackets = 0;
    int braces = 0;
    const auto at_boundary = [&] {
      return parens == 0 && brackets == 0 && braces == 0 &&
             (at(stop) || at(alternate_stop));
    };
    while (!at(TK::EndOfFile) && !at_boundary() &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_)) {
          break;
        }
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      const auto& grammar = grammar_scopes_.back();
      if (grammar.failed || grammar.interrupted ||
          !grammar.accepts(peek().kind)) {
        break;
      }
      switch (peek().kind) {
        case TK::OpenParenthesis:
          ++parens;
          break;
        case TK::CloseParenthesis:
          if (parens > 0) --parens;
          break;
        case TK::OpenBracket:
          ++brackets;
          break;
        case TK::CloseBracket:
          if (brackets > 0) --brackets;
          break;
        case TK::OpenBrace:
        case TK::ApostropheOpenBrace:
          ++braces;
          break;
        case TK::CloseBrace:
          if (braces > 0) --braces;
          break;
        default:
          break;
      }
      consumeInto(line);
    }
    if (!at(stop) || !grammar_scopes_.back().complete()) {
      recordGrammarFallback("for-header segment outside Annex A rule");
      static_cast<void>(endGrammar());
      while (!at(TK::EndOfFile) && !at(stop) && !at(alternate_stop) &&
             !(stop_at_conditional_boundary_ &&
               isConditionalBoundaryDirective(peek()))) {
        consumeInto(line);
      }
      return false;
    }
    static_cast<void>(endGrammar());
    return true;
  }

  auto consumeForHeader(Line& line, bool generate) -> bool {
    if (!at(TK::OpenParenthesis)) {
      recordGrammarFallback("for header requires '(' in Annex A");
      return false;
    }
    bool valid = true;
    consumeInto(line);
    if (!at(TK::Semicolon)) {
      valid &= consumeAnnexUntil(
          TK::Semicolon, TK::CloseParenthesis,
          generate ? std::vector<std::string_view>{"genvar_initialization"}
                   : std::vector<std::string_view>{"for_initialization"},
          line);
    } else if (generate) {
      valid = false;
      recordGrammarFallback("generate for requires genvar initialization");
    }
    if (at(TK::Semicolon)) {
      consumeInto(line);
    } else {
      valid = false;
    }
    if (!at(TK::Semicolon) && !at(TK::CloseParenthesis)) {
      valid &= consumeAnnexUntil(
          TK::Semicolon, TK::CloseParenthesis,
          generate ? std::vector<std::string_view>{"genvar_expression"}
                   : std::vector<std::string_view>{"expression"},
          line);
    } else if (generate) {
      valid = false;
      recordGrammarFallback("generate for requires genvar expression");
    }
    if (at(TK::Semicolon)) {
      consumeInto(line);
    } else {
      valid = false;
    }
    if (!at(TK::CloseParenthesis)) {
      valid &= consumeAnnexUntil(
          TK::CloseParenthesis, TK::EndOfFile,
          generate ? std::vector<std::string_view>{"genvar_iteration"}
                   : std::vector<std::string_view>{"for_step"},
          line);
    } else if (generate) {
      valid = false;
      recordGrammarFallback("generate for requires genvar iteration");
    }
    if (at(TK::CloseParenthesis)) {
      consumeInto(line);
    } else {
      valid = false;
    }
    return valid;
  }

  auto consumeUntilSemi() -> void {
    while (pos_ < tokens_.size() && !at(TK::Semicolon) && !at(TK::EndOfFile)) {
      if (stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(peek())) {
        break;
      }
      if (matchingOpenFrame(peek().kind)) break;
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      consumeInto(line_);
    }
    if (at(TK::Semicolon)) {
      consumeInto(line_);
    }
    addLine();
  }

  auto warnUnsupported(Token tok, std::string_view construct) -> void {
    warnings_.push_back({
        .location = tok.location(),
        .code = "unsupported-construct",
        .message = "unsupported SystemVerilog construct '" +
                   std::string(construct) +
                   (recovery_enabled_ ? "'; original text preserved"
                                      : "'; original source unavailable"),
    });
  }

  [[nodiscard]] static auto unsupportedConstructName(Token tok)
      -> std::string_view {
    if (!tok.rawText().empty()) {
      return tok.rawText();
    }
    return "unknown";
  }

  enum class BlockLayout : std::uint8_t {
    Structural,
    Named,
    Simple,
    BeginEnd,
    Fork,
    Case,
    DelimitedRecovery,
  };

  struct BlockSpec {
    TK close_kind;
    BlockLayout layout;
  };

  // Closing tokens are also used to find a safe recovery point. A recovery
  // boundary says nothing about whether Annex A supports the construction.
  [[nodiscard]] static auto blockSpec(TK kind) -> std::optional<BlockSpec> {
    switch (kind) {
      case TK::ModuleKeyword:
      case TK::MacromoduleKeyword:
        return BlockSpec{.close_kind = TK::EndModuleKeyword,
                         .layout = BlockLayout::Structural};
      case TK::InterfaceKeyword:
        return BlockSpec{.close_kind = TK::EndInterfaceKeyword,
                         .layout = BlockLayout::Structural};
      case TK::PackageKeyword:
        return BlockSpec{.close_kind = TK::EndPackageKeyword,
                         .layout = BlockLayout::Structural};
      case TK::ProgramKeyword:
        return BlockSpec{.close_kind = TK::EndProgramKeyword,
                         .layout = BlockLayout::Structural};
      case TK::ClassKeyword:
        return BlockSpec{.close_kind = TK::EndClassKeyword,
                         .layout = BlockLayout::Named};
      case TK::FunctionKeyword:
        return BlockSpec{.close_kind = TK::EndFunctionKeyword,
                         .layout = BlockLayout::Named};
      case TK::TaskKeyword:
        return BlockSpec{.close_kind = TK::EndTaskKeyword,
                         .layout = BlockLayout::Named};
      case TK::GenerateKeyword:
        return BlockSpec{.close_kind = TK::EndGenerateKeyword,
                         .layout = BlockLayout::Simple};
      case TK::BeginKeyword:
        return BlockSpec{.close_kind = TK::EndKeyword,
                         .layout = BlockLayout::BeginEnd};
      case TK::ForkKeyword:
        return BlockSpec{.close_kind = TK::JoinKeyword,
                         .layout = BlockLayout::Fork};
      case TK::CaseKeyword:
      case TK::CaseXKeyword:
      case TK::CaseZKeyword:
        return BlockSpec{.close_kind = TK::EndCaseKeyword,
                         .layout = BlockLayout::Case};
      case TK::CoverGroupKeyword:
        return BlockSpec{.close_kind = TK::EndGroupKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      case TK::PropertyKeyword:
        return BlockSpec{.close_kind = TK::EndPropertyKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      case TK::SequenceKeyword:
        return BlockSpec{.close_kind = TK::EndSequenceKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      case TK::ClockingKeyword:
        return BlockSpec{.close_kind = TK::EndClockingKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      case TK::CheckerKeyword:
        return BlockSpec{.close_kind = TK::EndCheckerKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      case TK::SpecifyKeyword:
        return BlockSpec{.close_kind = TK::EndSpecifyKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      case TK::PrimitiveKeyword:
        return BlockSpec{.close_kind = TK::EndPrimitiveKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      case TK::ConfigKeyword:
        return BlockSpec{.close_kind = TK::EndConfigKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      case TK::TableKeyword:
        return BlockSpec{.close_kind = TK::EndTableKeyword,
                         .layout = BlockLayout::DelimitedRecovery};
      default:
        return std::nullopt;
    }
  }

  [[nodiscard]] static auto matchesBlockClose(TK expected, TK actual) -> bool {
    return actual == expected ||
           (expected == TK::JoinKeyword &&
            (actual == TK::JoinAnyKeyword || actual == TK::JoinNoneKeyword));
  }

  [[nodiscard]] auto recoveryBlockSpec(size_t index) const
      -> std::optional<BlockSpec> {
    const TK kind = tokens_[index].kind;
    if (index > 0) {
      const TK preceding = tokens_[index - 1].kind;
      // Annex A uses these keyword pairs inside assertion statements; they
      // do not open property_declaration or sequence_declaration blocks.
      if ((kind == TK::PropertyKeyword &&
           (preceding == TK::AssertKeyword ||
            preceding == TK::AssumeKeyword ||
            preceding == TK::CoverKeyword ||
            preceding == TK::RestrictKeyword)) ||
          (kind == TK::SequenceKeyword && preceding == TK::CoverKeyword)) {
        return std::nullopt;
      }
    }
    return blockSpec(kind);
  }

  [[nodiscard]] auto sourceLineStart(size_t index) const -> size_t {
    const size_t offset =
        std::min(tokens_[index].location().offset(), source_.size());
    if (offset == 0) {
      return 0;
    }
    const size_t newline = source_.find_last_of("\r\n", offset - 1);
    return newline == std::string_view::npos ? 0 : newline + 1;
  }

  [[nodiscard]] auto cleanLineStart(size_t index, size_t after) const -> bool {
    if (index >= tokens_.size() || tokens_[index].kind == TK::EndOfFile) {
      return false;
    }
    const size_t start = sourceLineStart(index);
    const size_t offset =
        std::min(tokens_[index].location().offset(), source_.size());
    if (start <= tokens_[after].location().offset()) {
      return false;
    }
    const auto leading = source_.substr(start, offset - start);
    return std::ranges::all_of(leading,
                               [](char ch) { return ch == ' ' || ch == '\t'; });
  }

  // Skip an unsupported block using the same delimiter table as the normal
  // parser. Inner blocks cannot terminate the outer unsupported block.
  [[nodiscard]] auto findPairedEnd(size_t start,
                                   TK close) const -> std::optional<size_t> {
    std::vector<TK> expected{close};
    for (size_t i = start + 1;
         i < tokens_.size() && tokens_[i].kind != TK::EndOfFile; ++i) {
      if (stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(tokens_[i])) {
        return std::nullopt;
      }
      if (auto nested = recoveryBlockSpec(i)) {
        expected.push_back(nested->close_kind);
      } else if (matchesBlockClose(expected.back(), tokens_[i].kind)) {
        expected.pop_back();
        if (expected.empty()) {
          size_t after = i + 1;
          if (after + 1 < tokens_.size() && tokens_[after].kind == TK::Colon &&
              tokens_[after + 1].kind == TK::Identifier) {
            after += 2;
          }
          return after;
        }
      }
    }
    return std::nullopt;
  }

  // A construct with no known delimiter can only be skipped up to the
  // enclosing block's closing token (or a conditional branch boundary).
  [[nodiscard]] auto findOuterBoundary(size_t start) const -> size_t {
    std::vector<TK> nested;
    for (size_t i = start + 1;
         i < tokens_.size() && tokens_[i].kind != TK::EndOfFile; ++i) {
      const TK kind = tokens_[i].kind;
      if (stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(tokens_[i]) &&
          cleanLineStart(i, start)) {
        return i;
      }
      if (auto block = recoveryBlockSpec(i)) {
        nested.push_back(block->close_kind);
        continue;
      }
      if (!nested.empty() && matchesBlockClose(nested.back(), kind)) {
        nested.pop_back();
        continue;
      }
      if (nested.empty() && !block_stack_.empty() &&
          matchesBlockClose(block_stack_.back().close_kind, kind)) {
        return i;
      }
    }
    return tokens_.size() - 1;
  }

  auto appendOpaqueRange(size_t begin, size_t end) -> void {
    begin = std::max(std::min(begin, source_.size()), preserved_source_end_);
    end = std::min(end, source_.size());
    if (end <= begin) {
      return;
    }
    lines_.push_back(
        Line{.tokens = {},
             .raw_text = std::string(source_.substr(begin, end - begin)),
             .is_opaque = true});
    preserved_source_end_ = end;
  }

  auto attachOpaqueTokens(size_t begin, size_t end) -> void {
    if (lines_.empty() || !lines_.back().is_opaque) {
      lines_.push_back(Line{.tokens = {}, .raw_text = {}, .is_opaque = true});
    }
    auto& out = lines_.back().tokens;
    out.insert(out.end(), tokens_.begin() + begin, tokens_.begin() + end);
  }

  // Include trivia after the previous formatted token. When resuming on a
  // clean source line, leave that line's indentation to the printer.
  auto emitOpaque(size_t begin, size_t resume) -> void {
    // The unsupported-construct diagnostic already identifies this fallback.
    for (auto& scope : grammar_scopes_) scope.interrupted = true;
    addLine();
    const size_t raw_begin =
        begin == 0 ? 0
                   : std::min(tokens_[begin - 1].location().offset() +
                                  tokens_[begin - 1].rawText().size(),
                              source_.size());
    const size_t raw_end =
        resume == tokens_.size() - 1 ? source_.size()
        : cleanLineStart(resume, begin)
            ? sourceLineStart(resume)
            : std::min(tokens_[resume].location().offset(), source_.size());
    appendOpaqueRange(raw_begin, raw_end);
    attachOpaqueTokens(begin, resume);
    pos_ = resume;
  }

  // The active Annex A chart decides where an item ends. Tokens are appended
  // to the output line as the chart advances; malformed items fall back to
  // opaque recovery at the enclosing block boundary.
  [[nodiscard]] auto leafCheckpoint() const -> LeafCheckpoint {
    return {pos_, line_, lines_.size(), preserved_source_end_, indent_level_};
  }

  auto recoverMalformedItem(const LeafCheckpoint& saved) -> void {
    if (!recovery_enabled_) {
      consumeUntilSemi();
      return;
    }
    lines_.resize(saved.output_size);
    line_ = saved.line;
    preserved_source_end_ = saved.preserved_source_end;
    indent_level_ = saved.indent_level;
    emitOpaque(saved.pos, findOuterBoundary(saved.pos));
  }

  auto parseGrammarLeaf(bool recover_to_outer = false,
                        std::optional<LeafCheckpoint> checkpoint = {},
                        bool stop_at_complete_semicolon = false,
                        bool keep_completed_line_open = false) -> void {
    const LeafCheckpoint saved = checkpoint.value_or(leafCheckpoint());
    const size_t start = saved.pos;
    bool aggregate_type = false;
    int aggregate_braces = 0;
    const bool constraint_block =
        at(TK::ConstraintKeyword) ||
        (at(TK::StaticKeyword) && at(TK::ConstraintKeyword, 1));
    int constraint_braces = 0;
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      if (!grammar_scopes_.empty() && grammar_scopes_.back().complete() &&
          !grammar_scopes_.back().accepts(peek().kind)) {
        if (!keep_completed_line_open) addLine();
        return;
      }
      if (at(TK::MacroUsage) ||
          (at(TK::Directive) && !isCompilerDirective(peek()))) {
        consumeInto(line_);
        consumeUntilSemi();
        return;
      }
      if (isConditionalStartDirective(peek()) && !grammar_scopes_.empty()) {
        bool leaf_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, leaf_ended, indent_level_)) {
          grammar_scopes_.back().interrupted = true;
          consumeUntilSemi();
          return;
        }
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (grammar_scopes_.empty() || grammar_scopes_.back().interrupted ||
          grammar_scopes_.back().failed) {
        consumeUntilSemi();
        return;
      }
      const auto& grammar = grammar_scopes_.back();
      if (pos_ == start && !grammar.accepts(peek().kind)) {
        recordGrammarFallback("item is outside this Annex A body rule");
        grammar_scopes_.back().interrupted = true;
        consumeUntilSemi();
        return;
      }
      if (!grammar.accepts(peek().kind)) break;
      const TK kind = peek().kind;
      if (kind == TK::StructKeyword || kind == TK::UnionKeyword) {
        aggregate_type = true;
      }
      if (aggregate_type && kind == TK::CloseBrace && aggregate_braces == 1) {
        addLine();
        if (indent_level_ > 0) --indent_level_;
      }
      if (constraint_block && kind == TK::CloseBrace &&
          constraint_braces == 1) {
        addLine();
        if (indent_level_ > 0) --indent_level_;
      }
      consumeInto(line_);
      if (stop_at_complete_semicolon && kind == TK::Semicolon &&
          grammar_scopes_.back().complete()) {
        addLine();
        return;
      }
      if (constraint_block && kind == TK::OpenBrace) {
        if (constraint_braces++ == 0) {
          addLine();
          ++indent_level_;
        }
      } else if (constraint_block && kind == TK::CloseBrace &&
                 constraint_braces > 0) {
        --constraint_braces;
      } else if (constraint_block && kind == TK::Semicolon &&
                 constraint_braces == 1) {
        addLine();
      }
      if (aggregate_type && kind == TK::OpenBrace) {
        if (aggregate_braces++ == 0) {
          addLine();
          ++indent_level_;
        }
      } else if (aggregate_type && kind == TK::CloseBrace &&
                 aggregate_braces > 0) {
        --aggregate_braces;
      } else if (aggregate_type && kind == TK::Semicolon &&
                 aggregate_braces == 1) {
        addLine();
      }
      if (grammar_scopes_.back().failed) break;
    }
    if (!grammar_scopes_.empty() && grammar_scopes_.back().complete()) {
      if (!keep_completed_line_open) addLine();
      return;
    }
    if (!recover_to_outer) {
      recordGrammarFallback(!grammar_scopes_.empty() &&
                                    grammar_scopes_.back().failed
                                ? grammar_scopes_.back().failure_reason
                                : "malformed Annex A item");
      if (!grammar_scopes_.empty()) grammar_scopes_.back().interrupted = true;
      indent_level_ = saved.indent_level;
      consumeUntilSemi();
      return;
    }
    if (!recovery_enabled_) {
      consumeUntilSemi();
      return;
    }
    if (start < tokens_.size()) {
      warnUnsupported(tokens_[start], unsupportedConstructName(tokens_[start]));
    }
    // No line produced by this item is retained when its source is emitted
    // opaquely. Earlier siblings stay intact, and the outer close is not read.
    lines_.resize(saved.output_size);
    line_ = saved.line;
    preserved_source_end_ = saved.preserved_source_end;
    indent_level_ = saved.indent_level;
    emitOpaque(start, findOuterBoundary(start));
  }

  auto parseOpaqueBlock(TK close) -> void {
    const size_t start = pos_;
    warnUnsupported(peek(), unsupportedConstructName(peek()));
    if (!recovery_enabled_) {
      consumeUntilSemi();
      return;
    }
    const auto after = findPairedEnd(start, close);
    const size_t resume = after ? *after : findOuterBoundary(start);
    emitOpaque(start, resume);
  }

  auto parseUnsupportedConstruct() -> void {
    const size_t start = pos_;
    warnUnsupported(peek(), unsupportedConstructName(peek()));
    if (!recovery_enabled_) {
      consumeUntilSemi();
      return;
    }
    emitOpaque(start, findOuterBoundary(start));
  }

  auto warnIncompatibleConditional(Token tok) -> void {
    warnings_.push_back({
        .location = tok.location(),
        .code = "incompatible-conditional-branches",
        .message = "conditional compilation branches leave incompatible parser "
                   "states; continuing with the first branch structure",
    });
  }

  // The next token starts on a new source line if its leading trivia has a
  // newline.
  [[nodiscard]] static auto hasLeadingNewline(Token tok) -> bool {
    for (auto trivia : tok.trivia()) {
      if (trivia.kind == TriviaKind::EndOfLine ||
          trivia.kind == TriviaKind::LineComment) {
        return true;
      }
    }
    return false;
  }

  // Optional `: label` after end/endmodule/endfunction/etc.
  auto consumeLabel() -> void {
    if (!at(TK::Colon)) return;
    if (!grammarAllows(TK::Colon)) {
      recordGrammarFallback("opening label outside Annex A rule");
      return;
    }
    consumeInto(line_);
    if (at(TK::Identifier) && grammarAllows(TK::Identifier)) {
      consumeInto(line_);
    } else {
      recordGrammarFallback("incomplete Annex A opening label");
    }
  }

  [[nodiscard]] auto snapshotState() const -> ParserState {
    return {
        .pos = pos_,
        .line = line_,
        .indent_level = indent_level_,
        .block_stack = block_stack_,
        .grammar_scopes = grammar_scopes_,
        .grammar_checkpoints = grammar_checkpoints_,
        .grammar_paused = grammar_paused_,
        .grammar_summary_owner = grammar_summary_owner_,
        .grammar_contexts = grammar_contexts_,
    };
  }

  auto restoreState(const ParserState& state) -> void {
    pos_ = state.pos;
    line_ = state.line;
    indent_level_ = state.indent_level;
    block_stack_ = state.block_stack;
    grammar_scopes_ = state.grammar_scopes;
    grammar_checkpoints_ = state.grammar_checkpoints;
    grammar_paused_ = state.grammar_paused;
    grammar_summary_owner_ = state.grammar_summary_owner;
    grammar_contexts_ = state.grammar_contexts;
  }

  [[nodiscard]] auto structuralStateCompatible(
      const ParserState& lhs, const ParserState& rhs) const -> bool {
    if (lhs.indent_level != rhs.indent_level ||
        lhs.block_stack.size() != rhs.block_stack.size() ||
        lhs.grammar_contexts != rhs.grammar_contexts ||
        lhs.grammar_scopes.size() != rhs.grammar_scopes.size() ||
        lhs.grammar_checkpoints.size() != rhs.grammar_checkpoints.size() ||
        lhs.grammar_paused != rhs.grammar_paused ||
        lhs.grammar_summary_owner != rhs.grammar_summary_owner) {
      return false;
    }
    for (size_t i = 0; i < lhs.block_stack.size(); ++i) {
      const auto& left = lhs.block_stack[i];
      const auto& right = rhs.block_stack[i];
      if (left.close_kind != right.close_kind ||
          left.extra_dedent_after_close != right.extra_dedent_after_close ||
          left.grammar_body != right.grammar_body ||
          ((left.close_kind == TK::EndConfigKeyword ||
            left.close_kind == TK::EndPrimitiveKeyword) &&
           left.statement_phase != right.statement_phase)) {
        return false;
      }
    }
    for (size_t i = 0; i < lhs.grammar_scopes.size(); ++i) {
      const auto& left = lhs.grammar_scopes[i];
      const auto& right = rhs.grammar_scopes[i];
      if (left.roots != right.roots || left.failed != right.failed ||
          left.interrupted != right.interrupted) {
        return false;
      }
    }
    return true;
  }

  [[nodiscard]] auto joinStates(const std::vector<ParserState>& states) const
      -> std::optional<ParserState> {
    if (states.empty()) {
      return std::nullopt;
    }

    ParserState joined = states.front();
    joined.pos = pos_;
    joined.line = Line{};
    for (const auto& state : states) {
      if (!structuralStateCompatible(joined, state)) {
        return std::nullopt;
      }
      for (size_t i = 0; i < joined.block_stack.size(); ++i) {
        joined.block_stack[i].statement_phase |=
            state.block_stack[i].statement_phase;
        joined.block_stack[i].udp_has_entry &=
            state.block_stack[i].udp_has_entry;
        joined.block_stack[i].udp_sequential |=
            state.block_stack[i].udp_sequential;
        joined.block_stack[i].udp_combinational |=
            state.block_stack[i].udp_combinational;
        joined.block_stack[i].udp_port_on_all_paths &=
            state.block_stack[i].udp_port_on_all_paths;
        joined.block_stack[i].udp_port_on_any_path |=
            state.block_stack[i].udp_port_on_any_path;
        joined.block_stack[i].udp_initial_seen |=
            state.block_stack[i].udp_initial_seen;
      }
      for (size_t i = 0; i < joined.grammar_scopes.size(); ++i) {
        joined.grammar_scopes[i].addContinuation(state.grammar_scopes[i]);
      }
    }
    return joined;
  }

  [[nodiscard]] auto parseBranch(const ParserState& state) -> BranchResult {
    const ParserState outer = snapshotState();
    auto outer_lines = std::move(lines_);
    auto outer_warnings = std::move(warnings_);
    const size_t outer_source_end = preserved_source_end_;
    const size_t outer_warning_pos = last_grammar_warning_pos_;
    const bool outer_stop = stop_at_conditional_boundary_;
    const bool outer_suspension = grammar_suspended_;

    restoreState(state);
    lines_.clear();
    warnings_.clear();
    stop_at_conditional_boundary_ = true;
    parseLevel(TK::EndOfFile);
    BranchResult result = {
        .state = snapshotState(),
        .lines = std::move(lines_),
        .warnings = std::move(warnings_),
        .preserved_source_end = preserved_source_end_,
    };

    restoreState(outer);
    lines_ = std::move(outer_lines);
    warnings_ = std::move(outer_warnings);
    preserved_source_end_ = outer_source_end;
    last_grammar_warning_pos_ = outer_warning_pos;
    stop_at_conditional_boundary_ = outer_stop;
    grammar_suspended_ = outer_suspension;
    return result;
  }

  auto appendBranchResult(BranchResult& branch) -> void {
    lines_.insert(lines_.end(), std::make_move_iterator(branch.lines.begin()),
                  std::make_move_iterator(branch.lines.end()));
    warnings_.insert(warnings_.end(),
                     std::make_move_iterator(branch.warnings.begin()),
                     std::make_move_iterator(branch.warnings.end()));
    preserved_source_end_ = branch.preserved_source_end;
  }

  [[nodiscard]] auto matchingOpenFrame(TK kind) const -> bool {
    return !block_stack_.empty() &&
           matchesBlockClose(block_stack_.back().close_kind, kind);
  }

  [[nodiscard]] static auto closeAllowsLabel(TK kind) -> bool {
    switch (kind) {
      case TK::EndModuleKeyword:
      case TK::EndInterfaceKeyword:
      case TK::EndPackageKeyword:
      case TK::EndProgramKeyword:
      case TK::EndClassKeyword:
      case TK::EndFunctionKeyword:
      case TK::EndTaskKeyword:
      case TK::EndKeyword:
      case TK::JoinKeyword:
      case TK::EndGroupKeyword:
      case TK::EndPropertyKeyword:
      case TK::EndSequenceKeyword:
      case TK::EndClockingKeyword:
      case TK::EndCheckerKeyword:
      case TK::EndPrimitiveKeyword:
      case TK::EndConfigKeyword:
        return true;
      default:
        return false;
    }
  }

  auto parseOpenFrameClose() -> void {
    if (block_stack_.empty()) {
      parseUnsupportedConstruct();
      return;
    }

    const BlockFrame frame = block_stack_.back();
    block_stack_.pop_back();
    if (indent_level_ > 0) {
      --indent_level_;
    }
    consumeInto(line_);
    if (at(TK::Colon)) {
      if (closeAllowsLabel(frame.close_kind) && at(TK::Identifier, 1)) {
        consumeInto(line_);
        consumeInto(line_);
      } else {
        recordGrammarFallback("closing label outside Annex A rule");
      }
    }
    addLine();
    indent_level_ = (indent_level_ >= frame.extra_dedent_after_close)
                        ? indent_level_ - frame.extra_dedent_after_close
                        : 0;
  }

  auto pushOpenFrame(TK closeKind) -> void {
    block_stack_.push_back(BlockFrame{.close_kind = closeKind,
                                      .extra_dedent_after_close = 0,
                                      .grammar_body = {}});
  }

  auto parseDelimitedBody(TK closeKind, std::string_view bodyRule = {},
                          bool constructorBody = false) -> void {
    pushOpenFrame(closeKind);
    block_stack_.back().grammar_body = bodyRule;
    block_stack_.back().constructor_body = constructorBody;
    ++indent_level_;
    parseLevel(closeKind);
    if (matchesBlockClose(closeKind, peek().kind)) {
      parseOpenFrameClose();
    } else if (!(stop_at_conditional_boundary_ &&
                 isConditionalBoundaryDirective(peek()))) {
      recordGrammarFallback("incomplete block before outer boundary");
    }
  }

  auto parseIndentedStatement(std::vector<std::string_view> roots = {
                                  "statement_or_null", "generate_block",
                                  "generate_item"}) -> void {
    const size_t stack_size_before = block_stack_.size();
    if (!stop_at_conditional_boundary_ && !grammar_scopes_.empty() &&
        !grammar_scopes_.back().failed && !grammar_scopes_.back().interrupted &&
        !grammar_paused_.back()) {
      const auto& waiting = grammar_scopes_.back().charts.back().waiting;
      std::vector<std::string_view> expected;
      for (const auto root : roots) {
        if (waiting.contains(annexRule(root))) expected.push_back(root);
      }
      if (!expected.empty()) roots = std::move(expected);
    }
    ++indent_level_;
    grammar_contexts_.push_back({block_stack_.size(), std::move(roots)});
    parseStatement();
    grammar_contexts_.pop_back();
    if (block_stack_.size() == stack_size_before) {
      --indent_level_;
    } else if (!block_stack_.empty()) {
      ++block_stack_.back().extra_dedent_after_close;
    }
  }

  auto recordGrammarFallback(std::string_view reason) -> void {
    if (last_grammar_warning_pos_ == pos_) return;
    last_grammar_warning_pos_ = pos_;
    warnings_.push_back({.location = peek().location(),
                         .code = "annex-a-fallback",
                         .message = "Annex A construction unavailable (" +
                                    std::string(reason) + ") at '" +
                                    std::string(peek().rawText()) +
                                    "'; original tokens preserved"});
  }

  [[nodiscard]] auto grammarRoots() const -> std::vector<std::string_view> {
    for (auto it = grammar_contexts_.rbegin(); it != grammar_contexts_.rend();
         ++it) {
      if (it->block_depth == block_stack_.size()) return it->roots;
    }
    if (block_stack_.empty()) {
      return {"description", "timeunits_declaration", "library_description"};
    }
    if (!block_stack_.back().grammar_body.empty()) {
      if (block_stack_.back().grammar_body == "config_body") {
        return block_stack_.back().statement_phase
                   ? std::vector<std::string_view>{"config_rule_statement"}
                   : std::vector<std::string_view>{
                         "local_parameter_declaration", "design_statement"};
      }
      if (block_stack_.back().grammar_body == "udp_body") {
        const auto& udp = block_stack_.back();
        if (udp.statement_phase) return {};
        std::vector<std::string_view> roots;
        if (!udp.udp_initial_seen) {
          if (!udp.udp_ansi_header) roots.push_back("udp_port_declaration");
          roots.push_back("udp_initial_statement");
          roots.push_back("combinational_body");
        }
        roots.push_back("sequential_body");
        return roots;
      }
      if (block_stack_.back().grammar_body == "udp_table_entry") {
        std::vector<std::string_view> roots;
        if (!block_stack_.back().udp_sequential)
          roots.push_back("combinational_entry");
        if (!block_stack_.back().udp_combinational)
          roots.push_back("sequential_entry");
        return roots;
      }
      return {block_stack_.back().grammar_body};
    }
    switch (block_stack_.back().close_kind) {
      case TK::EndModuleKeyword:
        return {"module_item"};
      case TK::EndInterfaceKeyword:
        return {"interface_item"};
      case TK::EndProgramKeyword:
        return {"program_item"};
      case TK::EndPackageKeyword:
        return {"package_item"};
      case TK::EndClassKeyword:
        return {"class_item"};
      case TK::EndGenerateKeyword:
        return {"generate_item"};
      case TK::EndFunctionKeyword:
        if (block_stack_.back().constructor_body) {
          return block_stack_.back().statement_phase
                     ? std::vector<std::string_view>{
                           "function_statement_or_null"}
                     : std::vector<std::string_view>{
                           "block_item_declaration",
                           "function_statement_or_null"};
        }
        return block_stack_.back().statement_phase
                   ? std::vector<std::string_view>{"function_statement_or_null"}
                   : std::vector<std::string_view>{
                         "tf_item_declaration", "block_item_declaration",
                         "function_statement_or_null"};
      case TK::EndTaskKeyword:
        return block_stack_.back().statement_phase
                   ? std::vector<std::string_view>{"statement_or_null"}
                   : std::vector<std::string_view>{"tf_item_declaration",
                                                   "block_item_declaration",
                                                   "statement_or_null"};
      case TK::EndCaseKeyword:
        return {"case_item", "case_generate_item"};
      case TK::EndKeyword:
      case TK::JoinKeyword:
        return block_stack_.back().statement_phase
                   ? std::vector<std::string_view>{"statement_or_null"}
                   : std::vector<std::string_view>{"block_item_declaration",
                                                   "statement_or_null"};
      default:
        return {"statement_or_null"};
    }
  }

  auto beginGrammar(std::vector<std::string_view> roots,
                    bool resumable_item = false) -> void {
    grammar_checkpoints_.push_back(
        resumable_item && !grammar_scopes_.empty()
            ? std::optional{grammar_scopes_.back().checkpoint()}
            : std::nullopt);
    grammar_scopes_.emplace_back(roots);
    grammar_paused_.push_back(false);
    grammar_summary_owner_.push_back(false);
  }

  // The parent chart can consume a completed child nonterminal directly.
  // Pause it while that child is parsed, then advance it once at endGrammar().
  auto summarizeChildInParent() -> void {
    if (grammar_scopes_.size() < 2 || !grammar_checkpoints_.back()) return;
    const size_t parent_index = grammar_scopes_.size() - 2;
    const auto& parent = grammar_scopes_[parent_index];
    if (grammar_paused_[parent_index] || parent.failed || parent.interrupted)
      return;
    const auto& waiting = parent.charts.back().waiting;
    const auto& roots = grammar_scopes_.back().roots;
    bool has_candidate = false;
    bool all_candidates_waited = true;
    for (const uint16_t root : roots) {
      if (!annexCanStart(kRuleNames[root], peek().kind)) continue;
      has_candidate = true;
      all_candidates_waited &= waiting.contains(root);
    }
    if (has_candidate && all_candidates_waited) {
      grammar_paused_[parent_index] = true;
      grammar_summary_owner_.back() = true;
    }
  }

  [[nodiscard]] auto grammarAllows(TK kind) const -> bool {
    if (grammar_scopes_.empty() || grammar_scopes_.back().failed ||
        grammar_scopes_.back().interrupted) {
      return true;
    }
    return grammar_scopes_.back().accepts(kind);
  }

  auto endGrammar(bool require_complete = true) -> AnnexState {
    AnnexState state = std::move(grammar_scopes_.back());
    const bool summarized = grammar_summary_owner_.back();
    grammar_scopes_.pop_back();
    grammar_paused_.pop_back();
    grammar_summary_owner_.pop_back();
    const auto checkpoint = grammar_checkpoints_.back();
    grammar_checkpoints_.pop_back();
    if (state.lost_continuation) {
      state.interrupted = true;
      recordGrammarFallback("conditional Annex A continuation became invalid");
    }
    if (checkpoint && !grammar_scopes_.empty() &&
        (summarized || !grammar_paused_.back())) {
      if (summarized) grammar_paused_.back() = false;
      if (summarized || state.failed || state.interrupted) {
        std::vector<uint16_t> completed_roots;
        if (summarized && state.complete()) {
          for (const uint16_t root : state.roots) {
            if (state.completed(kRuleNames[root]) &&
                grammar_scopes_.back()
                    .charts[checkpoint->chart_count - 1]
                    .waiting.contains(root)) {
              completed_roots.push_back(root);
            }
          }
        } else {
          completed_roots = state.roots;
          if (summarized && !state.failed && !state.interrupted) {
            state.interrupted = true;
            recordGrammarFallback("incomplete summarized Annex A child");
          }
        }
        if (!grammar_scopes_.back().skipOpaqueItem(*checkpoint,
                                                   completed_roots)) {
          recordGrammarFallback("Annex A parent cannot resume after child");
        }
      }
    }
    if (state.failed && !state.interrupted) {
      recordGrammarFallback(state.failure_reason);
    } else if (require_complete && !state.failed && !state.interrupted &&
               !state.complete() &&
               !(stop_at_conditional_boundary_ &&
                 isConditionalBoundaryDirective(peek()))) {
      recordGrammarFallback("incomplete Annex A construction");
    }
    return state;
  }

  auto interruptGrammar(std::string_view reason) -> void {
    bool interrupted = false;
    for (auto& scope : grammar_scopes_) {
      if (!scope.failed && !scope.interrupted) {
        scope.interrupted = true;
        interrupted = true;
      }
    }
    if (interrupted) recordGrammarFallback(reason);
  }

  // ---- grammar ----

  // NOLINTBEGIN(misc-no-recursion)

  auto parseLevel(TK stopKind) -> void {
    while (pos_ < tokens_.size()) {
      auto kind = peek().kind;
      if (matchesBlockClose(stopKind, kind) || kind == TK::EndOfFile) {
        break;
      }
      if (stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(peek())) {
        break;
      }
      parseStatement();
    }
  }

  // description ::= module_declaration | udp_declaration |
  // interface_declaration | program_declaration | package_declaration |
  // ... | config_declaration. The keyword alternatives enter their rule
  // functions directly; shared-prefix alternatives still use local grammar
  // state in parseStatement().
  auto parseDescriptionRule() -> bool {
    switch (peek().kind) {
      case TK::ModuleKeyword:
      case TK::MacromoduleKeyword:
        parseStructuralBlock(TK::EndModuleKeyword);
        return true;
      case TK::InterfaceKeyword:
        if (at(TK::ClassKeyword, 1))
          return parsePackageOrGenerateDeclarationRule();
        parseStructuralBlock(TK::EndInterfaceKeyword);
        return true;
      case TK::ProgramKeyword:
        if (at(TK::Semicolon, 1)) return parseAnonymousProgramRule();
        parseStructuralBlock(TK::EndProgramKeyword);
        return true;
      case TK::PackageKeyword:
        parseStructuralBlock(TK::EndPackageKeyword);
        return true;
      case TK::PrimitiveKeyword:
        parsePrimitiveBlock();
        return true;
      case TK::ConfigKeyword:
        parseConfigBlock();
        return true;
      case TK::ClassKeyword:
      case TK::TaskKeyword:
      case TK::FunctionKeyword:
      case TK::CheckerKeyword:
      case TK::CoverGroupKeyword:
      case TK::PropertyKeyword:
      case TK::SequenceKeyword:
        return parsePackageOrGenerateDeclarationRule();
      case TK::VirtualKeyword:
        return at(TK::ClassKeyword, 1) &&
               parsePackageOrGenerateDeclarationRule();
      default:
        return false;
    }
  }

  // module_item ::= port_declaration ';' | non_port_module_item. Enter the
  // distinct non_port_module_item productions here; shared-prefix ports,
  // declarations and instantiations retain their local item chart.
  auto parseModuleItemRule(bool allow_port_declaration) -> bool {
    if (parseTimeunitsRule()) return true;
    if (allow_port_declaration &&
        (at(TK::InputKeyword) || at(TK::OutputKeyword) ||
         at(TK::InOutKeyword) || at(TK::RefKeyword))) {
      parseAnnexSemicolonItem("port_declaration");
      return true;
    }
    if (parseParameterDeclarationRule()) return true;
    switch (peek().kind) {
      case TK::GenerateKeyword:
        parseSimpleBlock(TK::EndGenerateKeyword);
        return true;
      case TK::ModuleKeyword:
      case TK::MacromoduleKeyword:
        parseStructuralBlock(TK::EndModuleKeyword);
        return true;
      case TK::InterfaceKeyword:
        if (at(TK::ClassKeyword, 1)) return false;
        parseStructuralBlock(TK::EndInterfaceKeyword);
        return true;
      case TK::ProgramKeyword:
        parseStructuralBlock(TK::EndProgramKeyword);
        return true;
      case TK::SpecifyKeyword:
        parseAnnexDelimitedBlock(TK::EndSpecifyKeyword, "specify_block",
                                 "specify_item", false);
        return true;
      case TK::SpecParamKeyword:
        static_cast<void>(parseAnnexItem({"specparam_declaration"}, true));
        return true;
      default:
        break;
    }
    if (parseTypeDeclarationRule() || parseBuiltInDataDeclarationRule() ||
        parseNettypeDeclarationRule() || parseNetDeclarationRule() ||
        parseParameterOverrideRule() ||
        parseAssertionItemRule() || parseModuleCommonLeafRule() ||
        parsePackageOrGenerateDeclarationRule() ||
        parseGenerateConstructRule()) {
      return true;
    }
    if (at(TK::ClockingKeyword)) {
      parseAnnexDelimitedBlock(TK::EndClockingKeyword,
                               "clocking_declaration", "clocking_item");
      return true;
    }
    return parseProceduralConstructRule(true);
  }

  auto parseParameterOverrideRule() -> bool {
    if (!at(TK::DefParamKeyword)) return false;
    static_cast<void>(parseAnnexItem({"parameter_override"}, true));
    return true;
  }

  auto parseTimeunitsRule() -> bool {
    if (!at(TK::TimeUnitKeyword) && !at(TK::TimePrecisionKeyword))
      return false;
    static_cast<void>(parseAnnexItem({"timeunits_declaration"}));
    return true;
  }

  auto parseTypeDeclarationRule() -> bool {
    if (!at(TK::TypedefKeyword)) return false;
    static_cast<void>(parseAnnexItem({"type_declaration"}, true));
    return true;
  }

  auto parseNettypeDeclarationRule() -> bool {
    if (!at(TK::NetTypeKeyword)) return false;
    static_cast<void>(parseAnnexItem({"nettype_declaration"}, true));
    return true;
  }

  auto parseParameterDeclarationRule() -> bool {
    if (at(TK::ParameterKeyword)) {
      parseAnnexSemicolonItem("parameter_declaration");
      return true;
    }
    if (at(TK::LocalParamKeyword)) {
      parseAnnexSemicolonItem("local_parameter_declaration");
      return true;
    }
    return false;
  }

  auto parseBuiltInDataDeclarationRule() -> bool {
    switch (peek().kind) {
      case TK::BitKeyword:
      case TK::ByteKeyword:
      case TK::CHandleKeyword:
      case TK::EnumKeyword:
      case TK::EventKeyword:
      case TK::IntKeyword:
      case TK::IntegerKeyword:
      case TK::LogicKeyword:
      case TK::LongIntKeyword:
      case TK::RealKeyword:
      case TK::RealTimeKeyword:
      case TK::RegKeyword:
      case TK::ShortIntKeyword:
      case TK::ShortRealKeyword:
      case TK::StringKeyword:
      case TK::StructKeyword:
      case TK::TimeKeyword:
      case TK::UnionKeyword:
        static_cast<void>(parseAnnexItem({"data_declaration"}, true));
        return true;
      default:
        return false;
    }
  }

  auto parseNetDeclarationRule() -> bool {
    switch (peek().kind) {
      case TK::InterconnectKeyword:
      case TK::Supply0Keyword:
      case TK::Supply1Keyword:
      case TK::TriKeyword:
      case TK::Tri0Keyword:
      case TK::Tri1Keyword:
      case TK::TriAndKeyword:
      case TK::TriOrKeyword:
      case TK::TriRegKeyword:
      case TK::UWireKeyword:
      case TK::WAndKeyword:
      case TK::WireKeyword:
      case TK::WOrKeyword:
        static_cast<void>(parseAnnexItem({"net_declaration"}, true));
        return true;
      default:
        return false;
    }
  }

  // package_or_generate_item_declaration alternatives whose first terminal
  // identifies the declaration. Shared prefixes still use the local grammar.
  auto parsePackageOrGenerateDeclarationRule() -> bool {
    if (parseClassConstructorRule()) return true;
    if (at(TK::ImportKeyword)) {
      static_cast<void>(
          parseAnnexItem({"dpi_import_export", "data_declaration"}, true));
      return true;
    }
    if (at(TK::ExportKeyword)) {
      static_cast<void>(parseAnnexItem({"dpi_import_export"}, true));
      return true;
    }
    if (at(TK::ConstraintKeyword) ||
        (at(TK::StaticKeyword) && at(TK::ConstraintKeyword, 1))) {
      parseConstraintBlock({"extern_constraint_declaration"});
      return true;
    }
    if (at(TK::VirtualKeyword) && at(TK::ClassKeyword, 1)) {
      parseNamedBlock(TK::EndClassKeyword);
      return true;
    }
    switch (peek().kind) {
      case TK::TaskKeyword:
        parseNamedBlock(TK::EndTaskKeyword);
        return true;
      case TK::FunctionKeyword:
        parseNamedBlock(TK::EndFunctionKeyword);
        return true;
      case TK::CheckerKeyword:
        parseAnnexDelimitedBlock(TK::EndCheckerKeyword, "checker_declaration",
                                 "checker_or_generate_item");
        return true;
      case TK::ClassKeyword:
        parseNamedBlock(TK::EndClassKeyword);
        return true;
      case TK::InterfaceKeyword:
        if (!at(TK::ClassKeyword, 1)) return false;
        parseNamedBlock(TK::EndClassKeyword);
        return true;
      case TK::CoverGroupKeyword:
        parseAnnexDelimitedBlock(TK::EndGroupKeyword,
                                 "covergroup_declaration",
                                 "coverage_spec_or_option");
        return true;
      case TK::PropertyKeyword:
        parseAnnexWholeBlock(TK::EndPropertyKeyword, "property_declaration");
        return true;
      case TK::SequenceKeyword:
        parseAnnexWholeBlock(TK::EndSequenceKeyword, "sequence_declaration");
        return true;
      default:
        return false;
    }
  }

  // class_constructor_declaration has its own header and body production.
  // A local Annex A prefix distinguishes 'function new' and
  // 'function class_scope new' from function_declaration.
  auto parseClassConstructorRule() -> bool {
    if (!at(TK::FunctionKeyword)) return false;
    AnnexState candidate({"class_constructor_declaration"});
    bool constructor_name = false;
    for (size_t offset = 0; pos_ + offset < tokens_.size(); ++offset) {
      const TK kind = peek(offset).kind;
      if (isCompilerDirective(peek(offset)) ||
          !candidate.accepts(kind)) break;
      candidate.advance(peek(offset));
      if (kind == TK::NewKeyword &&
          candidate.hasViableRule("class_constructor_declaration")) {
        constructor_name = true;
        break;
      }
      if (kind == TK::Semicolon) break;
    }
    if (!constructor_name) return false;
    beginGrammar({"class_constructor_declaration"});
    consumeGrammarHeader(TK::EndFunctionKeyword,
                         {"class_constructor_declaration"});
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted ||
        !header.hasViableRule("class_constructor_declaration")) {
      recordGrammarFallback("invalid Annex A class constructor header");
    }
    parseDelimitedBody(TK::EndFunctionKeyword, {}, true);
    return true;
  }

  // class_item contains class methods, nested classes, constraints and
  // covergroups. These keyword alternatives call their declaration rules.
  auto parseClassItemRule() -> bool {
    if (parseParameterDeclarationRule()) return true;
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseBuiltInDataDeclarationRule())
      return true;
    if (at(TK::ConstraintKeyword) ||
        (at(TK::StaticKeyword) && at(TK::ConstraintKeyword, 1))) {
      parseConstraintBlock({"constraint_declaration"});
      return true;
    }
    if (at(TK::VirtualKeyword) && at(TK::ClassKeyword, 1)) {
      return parsePackageOrGenerateDeclarationRule();
    }
    if (at(TK::ExternKeyword)) {
      AnnexState choice({"class_method", "class_constraint"});
      for (size_t offset = 0; pos_ + offset < tokens_.size() &&
                              choice.accepts(peek(offset).kind);
           ++offset) {
        choice.advance(peek(offset));
        if (choice.hasViableRule("class_method") &&
            !choice.hasViableRule("class_constraint")) {
          static_cast<void>(parseAnnexItem({"class_method"}, true));
          return true;
        }
      }
    }
    if (at(TK::VirtualKeyword) || at(TK::StaticKeyword) ||
        at(TK::ProtectedKeyword) ||
        at(TK::LocalKeyword)) {
      AnnexState method({"class_method"});
      for (size_t prefix = 0; pos_ + prefix < tokens_.size(); ++prefix) {
        const TK next = peek(prefix).kind;
        // A pure virtual method can be a prototype ending in ';'. Its
        // declaration/prototype choice remains with the full item grammar.
        if (next == TK::PureKeyword) break;
        const bool method_body =
            (next == TK::FunctionKeyword &&
             (method.hasActiveRule("function_declaration") ||
              method.hasActiveRule("class_constructor_declaration"))) ||
            (next == TK::TaskKeyword &&
             method.hasActiveRule("task_declaration"));
        if (method_body) {
          beginGrammar({"class_method"});
          for (size_t i = 0; i < prefix; ++i) consumeInto(line_);
          const AnnexState qualifier = endGrammar(false);
          if (qualifier.failed || qualifier.interrupted ||
              !qualifier.hasViableRule("class_method")) {
            recordGrammarFallback("invalid Annex A class method qualifier");
            consumeUntilSemi();
            return true;
          }
          if (!parseClassConstructorRule()) {
            parseNamedBlock(next == TK::FunctionKeyword
                                ? TK::EndFunctionKeyword
                                : TK::EndTaskKeyword);
          }
          return true;
        }
        if (!method.accepts(next)) break;
        method.advance(peek(prefix));
      }
    }
    if (at(TK::RandKeyword) || at(TK::RandCKeyword) ||
        at(TK::ConstKeyword)) {
      static_cast<void>(parseAnnexItem({"class_property"}, true));
      return true;
    }
    if (at(TK::StaticKeyword) || at(TK::ProtectedKeyword) ||
        at(TK::LocalKeyword)) {
      // A class_item_qualifier also starts a method or constraint. Advance a
      // local Annex A choice only through the common prefix, then enter the
      // property rule when the other alternatives have been ruled out.
      AnnexState choice({"class_property", "class_method",
                         "class_constraint"});
      for (size_t offset = 0; pos_ + offset < tokens_.size() &&
                              choice.accepts(peek(offset).kind);
           ++offset) {
        choice.advance(peek(offset));
        if (choice.hasViableRule("class_property") &&
            !choice.hasViableRule("class_method") &&
            !choice.hasViableRule("class_constraint")) {
          static_cast<void>(parseAnnexItem({"class_property"}, true));
          return true;
        }
      }
    }
    switch (peek().kind) {
      case TK::TaskKeyword:
      case TK::FunctionKeyword:
      case TK::ClassKeyword:
      case TK::CoverGroupKeyword:
        return parsePackageOrGenerateDeclarationRule();
      case TK::InterfaceKeyword:
        return at(TK::ClassKeyword, 1) &&
               parsePackageOrGenerateDeclarationRule();
      default:
        return false;
    }
  }

  // checker_or_generate_item_declaration excludes task and class
  // declarations, unlike package_or_generate_item_declaration.
  auto parseCheckerDeclarationRule() -> bool {
    switch (peek().kind) {
      case TK::FunctionKeyword:
      case TK::CheckerKeyword:
      case TK::CoverGroupKeyword:
      case TK::PropertyKeyword:
      case TK::SequenceKeyword:
        return parsePackageOrGenerateDeclarationRule();
      case TK::ClockingKeyword:
        parseAnnexDelimitedBlock(TK::EndClockingKeyword,
                                 "clocking_declaration", "clocking_item");
        return true;
      default:
        return false;
    }
  }

  auto parseInterfaceItemRule(bool allow_port_declaration) -> bool {
    if (parseTimeunitsRule()) return true;
    if (allow_port_declaration &&
        (at(TK::InputKeyword) || at(TK::OutputKeyword) ||
         at(TK::InOutKeyword) || at(TK::RefKeyword))) {
      parseAnnexSemicolonItem("port_declaration");
      return true;
    }
    if (parseParameterDeclarationRule()) return true;
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseBuiltInDataDeclarationRule() || parseNetDeclarationRule())
      return true;
    if (at(TK::ModPortKeyword)) {
      static_cast<void>(parseAnnexItem({"modport_declaration"}, true));
      return true;
    }
    if (at(TK::ExternKeyword) &&
        (at(TK::FunctionKeyword, 1) || at(TK::TaskKeyword, 1) ||
         at(TK::ForkJoinKeyword, 1))) {
      static_cast<void>(parseAnnexItem({"extern_tf_declaration"}, true));
      return true;
    }
    if (at(TK::InterfaceKeyword) && !at(TK::ClassKeyword, 1)) {
      parseStructuralBlock(TK::EndInterfaceKeyword);
      return true;
    }
    if (at(TK::ProgramKeyword)) {
      parseStructuralBlock(TK::EndProgramKeyword);
      return true;
    }
    if (at(TK::GenerateKeyword)) {
      parseSimpleBlock(TK::EndGenerateKeyword);
      return true;
    }
    if (parseProceduralConstructRule(true)) return true;
    if (at(TK::ClockingKeyword)) {
      parseAnnexDelimitedBlock(TK::EndClockingKeyword,
                               "clocking_declaration", "clocking_item");
      return true;
    }
    return parseAssertionItemRule() ||
           parseModuleCommonLeafRule() ||
           parsePackageOrGenerateDeclarationRule() ||
           parseGenerateConstructRule();
  }

  auto parseProgramItemRule(bool allow_port_declaration) -> bool {
    if (parseTimeunitsRule()) return true;
    if (allow_port_declaration &&
        (at(TK::InputKeyword) || at(TK::OutputKeyword) ||
         at(TK::InOutKeyword) || at(TK::RefKeyword))) {
      parseAnnexSemicolonItem("port_declaration");
      return true;
    }
    if (parseParameterDeclarationRule()) return true;
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseBuiltInDataDeclarationRule() || parseNetDeclarationRule())
      return true;
    if (at(TK::GenerateKeyword)) {
      parseSimpleBlock(TK::EndGenerateKeyword);
      return true;
    }
    if (parseProceduralConstructRule(false)) return true;
    if (at(TK::ClockingKeyword)) {
      parseAnnexDelimitedBlock(TK::EndClockingKeyword,
                               "clocking_declaration", "clocking_item");
      return true;
    }
    return parseConcurrentAssertionRule() ||
           parseModuleCommonLeafRule(true) ||
           parsePackageOrGenerateDeclarationRule() ||
           parseGenerateConstructRule();
  }

  // generate_item ::= module_or_generate_item |
  // interface_or_generate_item | checker_or_generate_item.
  auto parseGenerateItemRule() -> bool {
    if (parseParameterDeclarationRule()) return true;
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseBuiltInDataDeclarationRule() || parseNetDeclarationRule() ||
        parseParameterOverrideRule())
      return true;
    if (at(TK::GenerateKeyword)) {
      parseSimpleBlock(TK::EndGenerateKeyword);
      return true;
    }
    if (parseProceduralConstructRule(true)) return true;
    if (at(TK::ClockingKeyword)) {
      parseAnnexDelimitedBlock(TK::EndClockingKeyword,
                               "clocking_declaration", "clocking_item");
      return true;
    }
    return parseAssertionItemRule() ||
           parseModuleCommonLeafRule() ||
           parsePackageOrGenerateDeclarationRule() ||
           parseGenerateConstructRule();
  }

  auto parseCheckerItemRule() -> bool {
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseBuiltInDataDeclarationRule())
      return true;
    return parseAssertionItemRule() ||
           parseModuleCommonLeafRule(true) ||
           parseCheckerDeclarationRule() || parseGenerateConstructRule() ||
           parseProceduralConstructRule(true);
  }

  auto parsePackageItemRule() -> bool {
    if (parseTimeunitsRule()) return true;
    if (parseAnonymousProgramRule()) return true;
    if (at(TK::ExportKeyword)) {
      static_cast<void>(parseAnnexItem(
          {"package_export_declaration", "dpi_import_export"}, true));
      return true;
    }
    return parseParameterDeclarationRule() ||
           parseTypeDeclarationRule() ||
           parseNettypeDeclarationRule() ||
           parseBuiltInDataDeclarationRule() ||
           parseNetDeclarationRule() ||
           parsePackageOrGenerateDeclarationRule();
  }

  // interface_class_item ::= type_declaration |
  // { attribute_instance } interface_class_method |
  // local_parameter_declaration ';' | parameter_declaration ';' | ';'.
  auto parseInterfaceClassItemRule() -> bool {
    if (parseParameterDeclarationRule() || parseTypeDeclarationRule())
      return true;
    if (at(TK::PureKeyword) && at(TK::VirtualKeyword, 1)) {
      static_cast<void>(parseAnnexItem({"interface_class_method"}, true));
      return true;
    }
    return false;
  }

  // anonymous_program ::= 'program' ';' { anonymous_program_item }
  // 'endprogram'. Its header and each body item use their Annex A rules.
  auto parseAnonymousProgramRule() -> bool {
    if (!at(TK::ProgramKeyword) || !at(TK::Semicolon, 1)) return false;
    parseAnnexDelimitedBlock(TK::EndProgramKeyword, "anonymous_program",
                             "anonymous_program_item");
    return true;
  }

  auto parseAnonymousProgramItemRule() -> bool {
    switch (peek().kind) {
      case TK::TaskKeyword:
      case TK::FunctionKeyword:
      case TK::ClassKeyword:
      case TK::CoverGroupKeyword:
        return parsePackageOrGenerateDeclarationRule();
      case TK::InterfaceKeyword:
        return at(TK::ClassKeyword, 1) &&
               parsePackageOrGenerateDeclarationRule();
      default:
        return false;
    }
  }

  auto parseBlockOrTfItemDeclarationRule(bool allow_tf_port) -> bool {
    if (parseParameterDeclarationRule()) return true;
    if (at(TK::LetKeyword)) {
      static_cast<void>(parseAnnexItem({"let_declaration"}, true));
      return true;
    }
    if (allow_tf_port &&
        (at(TK::InputKeyword) || at(TK::OutputKeyword) ||
         at(TK::InOutKeyword) || at(TK::RefKeyword))) {
      static_cast<void>(parseAnnexItem({"tf_port_declaration"}, true));
      return true;
    }
    return parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
           parseBuiltInDataDeclarationRule();
  }

  auto parseProceduralConstructRule(bool allow_always) -> bool {
    const TK kind = peek().kind;
    if (kind != TK::InitialKeyword && kind != TK::FinalKeyword &&
        !(allow_always && (kind == TK::AlwaysKeyword ||
                           kind == TK::AlwaysCombKeyword ||
                           kind == TK::AlwaysFFKeyword ||
                           kind == TK::AlwaysLatchKeyword))) {
      return false;
    }
    parseProceduralBlock();
    return true;
  }

  // module_common_item has distinct leading terminals for these three leaf
  // productions. Program and checker items include continuous_assign, but
  // neither includes net_alias or bind_directive.
  auto parseModuleCommonLeafRule(bool continuous_only = false) -> bool {
    if (at(TK::GenVarKeyword)) {
      static_cast<void>(parseAnnexItem({"genvar_declaration"}, true));
      return true;
    }
    if (at(TK::AssignKeyword)) {
      static_cast<void>(parseAnnexItem({"continuous_assign"}, true));
      return true;
    }
    if (!continuous_only && at(TK::AliasKeyword)) {
      static_cast<void>(parseAnnexItem({"net_alias"}, true));
      return true;
    }
    if (!continuous_only && at(TK::BindKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      const AnnexState item = parseAnnexItem({"bind_directive"}, true);
      if (item.failed || item.interrupted || !item.complete()) {
        recoverMalformedItem(saved);
      }
      return true;
    }
    return false;
  }

  // statement_item ::= ... | case_statement | conditional_statement |
  // loop_statement | par_block | seq_block | randcase_statement | ... .
  // These alternatives have distinct leading terminals. Leaf alternatives
  // continue through their local Annex A rule below.
  auto parseStatementItemRule() -> bool {
    switch (peek().kind) {
      case TK::At:
      case TK::Hash:
      case TK::DoubleHash:
        parseProceduralTimingControlStatementRule();
        return true;
      case TK::AssertKeyword:
      case TK::AssumeKeyword:
        return parseAssertPropertyStatementRule() ||
               parseImmediateAssertionRule();
      case TK::CoverKeyword:
        return parseCoverAssertionRule() || parseImmediateAssertionRule();
      case TK::RestrictKeyword:
        return parseRestrictPropertyStatementRule();
      case TK::ExpectKeyword:
        return parseExpectPropertyStatementRule();
      case TK::BeginKeyword:
        parseBeginEnd(TK::EndKeyword);
        return true;
      case TK::ForkKeyword:
        parseFork(TK::JoinKeyword);
        return true;
      case TK::IfKeyword:
        parseIf(false);
        return true;
      case TK::CaseKeyword:
      case TK::CaseXKeyword:
      case TK::CaseZKeyword:
      case TK::RandCaseKeyword:
        parseCase(false);
        return true;
      case TK::ForKeyword:
      case TK::ForeachKeyword:
      case TK::WhileKeyword:
      case TK::RepeatKeyword:
      case TK::ForeverKeyword:
      case TK::DoKeyword:
        parseLoop(false);
        return true;
      case TK::RandSequenceKeyword:
        parseRandsequenceStatement();
        return true;
      case TK::WaitKeyword:
      case TK::WaitOrderKeyword:
        return parseWaitStatementRule();
      default:
        return false;
    }
  }

  // procedural_timing_control_statement ::= procedural_timing_control
  // statement_or_null. The control is one Annex A child; the body calls the
  // statement production while output lines are emitted from this pass.
  auto parseProceduralTimingControlStatementRule() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"procedural_timing_control_statement"});
    const bool control = consumeAnnexRule("procedural_timing_control", line_);
    const AnnexState prefix = endGrammar(false);
    if (!control || prefix.failed || prefix.interrupted ||
        !prefix.hasActiveRule("statement_or_null")) {
      recordGrammarFallback("invalid Annex A procedural timing control");
      recoverMalformedItem(saved);
      return;
    }
    const bool compound =
        at(TK::BeginKeyword) || at(TK::ForkKeyword) || at(TK::IfKeyword) ||
        at(TK::CaseKeyword) || at(TK::CaseXKeyword) ||
        at(TK::CaseZKeyword) || at(TK::ForKeyword) ||
        at(TK::ForeachKeyword) || at(TK::WhileKeyword) ||
        at(TK::RepeatKeyword) || at(TK::ForeverKeyword) || at(TK::DoKeyword);
    if (compound) {
      addLine();
      parseIndentedStatement({"statement_or_null"});
    } else {
      grammar_contexts_.push_back({block_stack_.size(), {"statement_or_null"}});
      parseStatement();
      grammar_contexts_.pop_back();
    }
  }

  // wait_statement ::= wait '(' expression ')' statement_or_null |
  // wait fork ';' | wait_order '(' identifier-list ')' action_block.
  auto parseWaitStatementRule() -> bool {
    if (at(TK::WaitOrderKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      beginGrammar({"wait_statement"});
      while (!at(TK::EndOfFile) &&
             !grammar_scopes_.back().hasActiveRule("action_block")) {
        if (isConditionalStartDirective(peek())) {
          bool header_ended = true;
          if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                     indent_level_))
            break;
          continue;
        }
        if (isCompilerDirective(peek())) {
          addLine();
          parseDirectiveLine();
          continue;
        }
        if (!grammar_scopes_.back().accepts(peek().kind)) break;
        consumeInto(line_);
      }
      const AnnexState prefix = endGrammar(false);
      if (prefix.failed || prefix.interrupted ||
          !prefix.hasActiveRule("action_block")) {
        recordGrammarFallback("invalid Annex A wait_order header");
        recoverMalformedItem(saved);
        return true;
      }
      parseActionBlockRule();
      return true;
    }
    if (!at(TK::WaitKeyword)) return false;
    if (!at(TK::OpenParenthesis, 1)) {
      static_cast<void>(parseAnnexItem({"wait_statement"}));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"wait_statement"});
    consumeInto(line_);  // wait
    consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                          "expression", line_);
    const AnnexState prefix = endGrammar(false);
    if (prefix.failed || prefix.interrupted ||
        !prefix.hasActiveRule("statement_or_null") ||
        line_.tokens.empty() ||
        line_.tokens.back().kind != TK::CloseParenthesis) {
      recordGrammarFallback("invalid Annex A wait condition");
      recoverMalformedItem(saved);
      return true;
    }
    addLine();
    parseIndentedStatement({"statement_or_null"});
    return true;
  }

  // conditional_statement and case_statement both start with the Annex A
  // unique_priority production. Parse that prefix as a rule, then enter the
  // selected statement production without a construction-wide selector.
  auto parseQualifiedStatementRule() -> bool {
    if (!at(TK::UniqueKeyword) && !at(TK::Unique0Keyword) &&
        !at(TK::PriorityKeyword)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"unique_priority"});
    consumeInto(line_);
    const AnnexState prefix = endGrammar();
    if (prefix.failed || prefix.interrupted ||
        !prefix.completed("unique_priority")) {
      recordGrammarFallback("invalid Annex A unique_priority");
      recoverMalformedItem(saved);
      return true;
    }
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek()) &&
           !isConditionalBoundaryDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if (at(TK::IfKeyword)) {
      parseIf(false);
    } else if (at(TK::CaseKeyword) || at(TK::CaseXKeyword) ||
               at(TK::CaseZKeyword)) {
      parseCase(false);
    } else {
      recordGrammarFallback("unique_priority requires Annex A if or case");
      recoverMalformedItem(saved);
    }
    return true;
  }

  // statement ::= [ block_identifier ':' ] { attribute_instance }
  // statement_item. Use the local grammar state for the label's shared
  // identifier prefix; the selected body rule is parsed by its own function.
  auto parseStatementLabelRule(
      const std::vector<std::string_view>& roots) -> bool {
    if (!at(TK::Identifier) || !at(TK::Colon, 1)) return false;
    AnnexState label(roots);
    label.advance(peek());
    label.advance(peek(1));
    if (label.failed) return false;
    for (const std::string_view body_rule :
         {"statement_item", "concurrent_assertion_statement",
          "deferred_immediate_assertion_statement"}) {
      if (label.hasActiveRule(body_rule)) {
        parseLabeledStatement(body_rule);
        return true;
      }
    }
    return false;
  }

  // conditional_generate_construct and loop_generate_construct are shared by
  // module, interface, program, checker and generate items in Annex A.
  auto parseGenerateConstructRule() -> bool {
    switch (peek().kind) {
      case TK::IfKeyword:
        parseIf(true);
        return true;
      case TK::CaseKeyword:
        parseCase(true);
        return true;
      case TK::ForKeyword:
        parseLoop(true);
        return true;
      default:
        return false;
    }
  }

  // generate_block ::= generate_item | [ identifier ':' ] begin
  // [ ':' identifier ] { generate_item } end [ ':' identifier ].
  auto parseGenerateBlockRule() -> void {
    if (at(TK::Identifier) && at(TK::Colon, 1) &&
        at(TK::BeginKeyword, 2)) {
      consumeInto(line_);
      consumeInto(line_);
    }
    if (at(TK::BeginKeyword)) {
      consumeInto(line_);
      consumeLabel();
      addLine();
      parseDelimitedBody(TK::EndKeyword, "generate_item");
      return;
    }
    grammar_contexts_.push_back({block_stack_.size(), {"generate_item"}});
    parseStatement();
    grammar_contexts_.pop_back();
  }

  // Enter the production selected by the enclosing rule. During a live
  // conditional continuation the enclosing chart stays active; the same
  // production functions still choose the construction to parse.
  auto parseDirectGrammarRule(bool active_continuation = false) -> bool {
    if (!active_continuation && !grammar_scopes_.empty()) return false;
    const auto roots = grammarRoots();
    for (const std::string_view root : roots) {
      if (root == "timeunits_declaration" && parseTimeunitsRule())
        return true;
      if (root == "description" && block_stack_.empty()) {
        if (parseDescriptionRule()) return true;
      }
      if (root == "generate_block") {
        parseGenerateBlockRule();
        return true;
      }
      if (root == "statement_or_null" || root == "statement" ||
          root == "function_statement_or_null" ||
          root == "function_statement") {
        if (parseStatementLabelRule(roots) ||
            parseQualifiedStatementRule()) return true;
        if (parseStatementItemRule()) return true;
      }
      if (root == "concurrent_assertion_statement") {
        if (parseConcurrentAssertionRule()) return true;
      }
      if (root == "statement_item") {
        if (parseQualifiedStatementRule() || parseStatementItemRule())
          return true;
      }
      if (root == "module_item" || root == "non_port_module_item") {
        if (parseModuleItemRule(root == "module_item")) return true;
      }
      if (root == "interface_item" || root == "non_port_interface_item") {
        if (parseInterfaceItemRule(root == "interface_item")) return true;
      }
      if (root == "program_item" || root == "non_port_program_item") {
        if (parseProgramItemRule(root == "program_item")) return true;
      }
      if (root == "generate_item") {
        if (parseGenerateItemRule()) return true;
      }
      if (root == "checker_or_generate_item") {
        if (parseCheckerItemRule()) return true;
      }
      if (root == "package_item") {
        if (parsePackageItemRule()) return true;
      }
      if (root == "anonymous_program_item") {
        if (parseAnonymousProgramItemRule()) return true;
      }
      if (root == "class_item") {
        if (parseClassItemRule()) return true;
      }
      if (root == "interface_class_item") {
        if (parseInterfaceClassItemRule()) return true;
      }
      if (root == "tf_item_declaration" ||
          root == "block_item_declaration") {
        if (parseBlockOrTfItemDeclarationRule(root == "tf_item_declaration"))
          return true;
      }
    }
    return false;
  }

  auto parseStatement() -> void {
    if (stop_at_conditional_boundary_ &&
        isConditionalBoundaryDirective(peek())) {
      return;
    }

    if (matchingOpenFrame(peek().kind)) {
      parseOpenFrameClose();
      return;
    }

    if (at(TK::Directive)) {
      if (!isCompilerDirective(peek())) {
        // An unexpanded macro can stand for one entire item. Keep its source
        // line, then resume the enclosing Annex A rule after that item.
        parseMacroStatement();
        return;
      }
      if (isConditionalStartDirective(peek())) {
        parseConditionalRegion();
      } else {
        parseDirectiveLine();
      }
      return;
    }

    // parseBranch() enters through parseLevel(), even when a conditional
    // directive is inside a case body. Keep each case item on its rule path
    // instead of treating the entire item and its nested statement as a leaf.
    if (!block_stack_.empty() &&
        block_stack_.back().close_kind == TK::EndCaseKeyword) {
      const auto roots = grammarRoots();
      if (roots.size() == 1 &&
          roots.front() == block_stack_.back().grammar_body) {
        parseCaseItem();
        return;
      }
    }

    // Consume complete Annex A attribute_instance prefixes before selecting
    // the construction they decorate. package_declaration stores these outside
    // package_item; other contexts validate them through their current root.
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const bool package_item =
          !block_stack_.empty() &&
          block_stack_.back().grammar_body == "package_item";
      beginGrammar(package_item
                       ? std::vector<std::string_view>{"attribute_instance"}
                       : grammarRoots());
      const size_t origin = grammar_scopes_.back().charts.size() - 1;
      do {
        consumeInto(line_);
      } while (
          !at(TK::EndOfFile) && !grammar_scopes_.back().failed &&
          !grammar_scopes_.back().interrupted &&
          !grammar_scopes_.back().completedFrom("attribute_instance", origin));
      const AnnexState prefix = endGrammar(false);
      if (prefix.failed || prefix.interrupted ||
          !prefix.completedFrom("attribute_instance", origin)) {
        recordGrammarFallback("incomplete Annex A attribute instance");
        consumeUntilSemi();
        return;
      }
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    }
    if (at(TK::Directive) && !isCompilerDirective(peek())) {
      parseMacroStatement();
      return;
    }

    if (grammar_scopes_.empty() && block_stack_.empty() &&
        parseDescriptionRule()) return;
    if (parseDirectGrammarRule()) return;

    if (!block_stack_.empty() &&
        block_stack_.back().grammar_body == "constraint_block_item") {
      static_cast<void>(parseAnnexItem({"constraint_block_item"}));
      return;
    }
    if (!block_stack_.empty() &&
        block_stack_.back().grammar_body == "config_body") {
      parseConfigItem();
      return;
    }
    if (!block_stack_.empty() &&
        block_stack_.back().grammar_body == "udp_body") {
      parseUdpBodyItem();
      return;
    }
    if (!block_stack_.empty() &&
        block_stack_.back().grammar_body == "udp_table_entry") {
      const AnnexState entry = parseAnnexItem(grammarRoots());
      auto& table = block_stack_.back();
      table.udp_combinational |= entry.completed("combinational_entry");
      table.udp_sequential |= entry.completed("sequential_entry");
      table.udp_has_entry |= entry.complete();
      return;
    }

    // One live Annex A chart selects the current construction. Declarations
    // with a repeated body transfer their header to a short-lived chart and
    // parse body items separately; every other construction keeps this chart
    // through the same token consumption that emits the output lines.
    beginGrammar(grammarRoots(), true);
    const auto segmented_header = [&] {
      constexpr std::string_view rules[] = {"module_ansi_header",
                                            "module_nonansi_header",
                                            "interface_ansi_header",
                                            "interface_nonansi_header",
                                            "program_ansi_header",
                                            "program_nonansi_header",
                                            "package_declaration",
                                            "class_declaration",
                                            "interface_class_declaration",
                                            "function_declaration",
                                            "task_declaration",
                                            "constraint_declaration",
                                            "extern_constraint_declaration",
                                            "covergroup_declaration",
                                            "checker_declaration",
                                            "clocking_declaration",
                                            "specify_block",
                                            "property_declaration",
                                            "sequence_declaration",
                                            "config_declaration",
                                            "udp_declaration",
                                            "always_construct",
                                            "initial_construct",
                                            "final_construct",
                                            "seq_block",
                                            "par_block",
                                            "case_statement",
                                            "case_generate_construct",
                                            "randcase_statement",
                                            "generate_region",
                                            "conditional_statement",
                                            "if_generate_construct",
                                            "loop_statement",
                                            "loop_generate_construct"};
      return std::ranges::any_of(rules, [&](std::string_view rule) {
        return grammar_scopes_.back().hasActiveRule(rule) &&
               annexCanStart(rule, peek().kind);
      });
    }();
    if (segmented_header) {
      summarizeChildInParent();
      const bool resume_parent = grammar_summary_owner_.back();
      const auto checkpoint = grammar_checkpoints_.back();
      const std::vector<uint16_t> roots = grammar_scopes_.back().roots;
      const size_t outer_depth = block_stack_.size();
      AnnexState selector = std::move(grammar_scopes_.back());
      grammar_scopes_.pop_back();
      grammar_checkpoints_.pop_back();
      grammar_paused_.pop_back();
      grammar_summary_owner_.pop_back();
      // The chart identifies a structural child that needs an item-sized
      // scope. Its production function makes the syntactic choice. A missing
      // function is an explicit fallback, never a second structural parser.
      if (!parseDirectGrammarRule(true)) {
        recordGrammarFallback("no direct Annex A production for structural item");
        if (const auto block = blockSpec(peek().kind)) {
          parseOpaqueBlock(block->close_kind);
        } else {
          parseUnsupportedConstruct();
        }
      }
      if (resume_parent && checkpoint) {
        grammar_paused_.back() = false;
        if (block_stack_.size() != outer_depth) {
          grammar_scopes_.back().interrupted = true;
          recordGrammarFallback("segmented Annex A block interrupted");
        } else if (!grammar_scopes_.back().skipOpaqueItem(*checkpoint, roots)) {
          recordGrammarFallback("Annex A parent cannot resume after block");
        }
      }
      return;
    }

    summarizeChildInParent();
    parseStatementLayout(grammar_scopes_.back());
    const AnnexState item = endGrammar();
    if (!block_stack_.empty() &&
        (block_stack_.back().close_kind == TK::EndFunctionKeyword ||
         block_stack_.back().close_kind == TK::EndTaskKeyword ||
         block_stack_.back().close_kind == TK::EndKeyword ||
         block_stack_.back().close_kind == TK::JoinKeyword) &&
        !item.completed("tf_item_declaration") &&
        !item.completed("block_item_declaration")) {
      block_stack_.back().statement_phase = true;
    }
  }

  auto parseStatementLayout(const AnnexState& selector) -> void {
    const TK first = peek().kind;
    if (first == TK::Identifier && at(TK::Colon, 1)) {
      AnnexState labeled = selector;
      labeled.advance(peek());
      labeled.advance(peek(1));
      if (!labeled.failed) {
        for (const std::string_view body_rule :
             {"statement_item", "concurrent_assertion_statement",
              "deferred_immediate_assertion_statement"}) {
          if (labeled.hasActiveRule(body_rule)) {
            parseLabeledStatement(body_rule);
            return;
          }
        }
      }
    }
    if (!block_stack_.empty() &&
        (block_stack_.back().grammar_body == "coverage_spec_or_option" ||
         block_stack_.back().grammar_body == "clocking_item" ||
         block_stack_.back().grammar_body == "specify_item") &&
        grammarAllows(first)) {
      parseGrammarLeaf();
      return;
    }

    if (first == TK::Identifier) {
      parseIdentifierItem();
    } else if (const auto block = blockSpec(first);
               block && (block->layout == BlockLayout::Structural ||
                         block->layout == BlockLayout::Named)) {
      recordGrammarFallback("block outside the current Annex A body rule");
      const auto after = findPairedEnd(pos_, block->close_kind);
      emitOpaque(pos_, after ? *after : findOuterBoundary(pos_));
    } else if (grammarAllows(first) || first == TK::AssignKeyword ||
               first == TK::InputKeyword || first == TK::OutputKeyword ||
               first == TK::InOutKeyword || first == TK::RefKeyword ||
               first == TK::WireKeyword || first == TK::RegKeyword ||
               first == TK::LogicKeyword || first == TK::BitKeyword ||
               first == TK::IntKeyword || first == TK::IntegerKeyword ||
               first == TK::TypedefKeyword || first == TK::ParameterKeyword ||
               first == TK::LocalParamKeyword) {
      parseGrammarLeaf();
    } else if (slang::parsing::LexerFacts::isKeyword(first) ||
               first == TK::Unknown || first == TK::Question ||
               first == TK::CloseParenthesis || first == TK::CloseBracket) {
      parseUnsupportedConstruct();
    } else {
      consumeUntilSemi();
    }
  }

  auto parseLabeledStatement(std::string_view body_rule) -> void {
    consumeInto(line_);  // label identifier
    consumeInto(line_);  // colon
    grammar_contexts_.push_back({block_stack_.size(), {body_rule}});
    parseStatement();
    grammar_contexts_.pop_back();
  }

  // action_block ::= statement_or_null |
  // [ statement ] 'else' statement_or_null. A recursive statement call owns
  // any nested else before this production considers its own else.
  auto parseActionBlockRule() -> void {
    const bool null_before_else = at(TK::Semicolon);
    if (!at(TK::ElseKeyword)) {
      grammar_contexts_.push_back({block_stack_.size(), {"statement_or_null"}});
      parseStatement();
      grammar_contexts_.pop_back();
    }
    if (!at(TK::ElseKeyword)) return;
    if (null_before_else) {
      recordGrammarFallback("Annex A action_block requires a statement before else");
    }
    consumeInto(line_);
    grammar_contexts_.push_back({block_stack_.size(), {"statement_or_null"}});
    parseStatement();
    grammar_contexts_.pop_back();
  }

  // concurrent_assertion_statement ::= assert_property_statement |
  // assume_property_statement | cover_property_statement |
  // cover_sequence_statement | restrict_property_statement.
  auto parseConcurrentAssertionRule() -> bool {
    return parseAssertPropertyStatementRule() || parseCoverAssertionRule() ||
           parseRestrictPropertyStatementRule();
  }

  // assertion_item also admits deferred_immediate_assertion_item. Its #0 or
  // final prefix is distinct from the simple immediate statement, and the
  // assertion production validates the complete header.
  auto parseAssertionItemRule() -> bool {
    if (parseConcurrentAssertionRule()) return true;
    if ((at(TK::AssertKeyword) || at(TK::AssumeKeyword) ||
         at(TK::CoverKeyword)) &&
        (at(TK::Hash, 1) || at(TK::FinalKeyword, 1))) {
      return parseImmediateAssertionRule();
    }
    return false;
  }

  auto parseRestrictPropertyStatementRule() -> bool {
    if (!at(TK::RestrictKeyword) || !at(TK::PropertyKeyword, 1))
      return false;
    static_cast<void>(parseAnnexItem({"restrict_property_statement"}, true));
    return true;
  }

  auto parseAssertPropertyStatementRule() -> bool {
    if ((!at(TK::AssertKeyword) && !at(TK::AssumeKeyword)) ||
        !at(TK::PropertyKeyword, 1))
      return false;
    const LeafCheckpoint saved = leafCheckpoint();
    const std::string_view rule = at(TK::AssertKeyword)
                                      ? "assert_property_statement"
                                      : "assume_property_statement";
    beginGrammar({rule});
    consumeInto(line_);  // assert / assume
    consumeInto(line_);  // property
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted ||
        !header.hasViableRule(rule) ||
        !at(TK::OpenParenthesis)) {
      recordGrammarFallback("invalid Annex A property assertion header");
      recoverMalformedItem(saved);
      return true;
    }
    consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                          "property_spec", line_);
    if (line_.tokens.empty() ||
        line_.tokens.back().kind != TK::CloseParenthesis) {
      recordGrammarFallback("incomplete Annex A property assertion");
      recoverMalformedItem(saved);
      return true;
    }
    parseActionBlockRule();
    return true;
  }

  // The property_spec / sequence_expr alternatives may have long shared
  // prefixes. Keep their local Annex A chart live until it expects the
  // statement_or_null child, then call that child directly.
  auto parseCoverAssertionRule() -> bool {
    if (!at(TK::CoverKeyword) ||
        (!at(TK::PropertyKeyword, 1) && !at(TK::SequenceKeyword, 1))) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const std::string_view rule = at(TK::PropertyKeyword, 1)
                                      ? "cover_property_statement"
                                      : "cover_sequence_statement";
    beginGrammar({rule});
    while (!at(TK::EndOfFile) &&
           !grammar_scopes_.back().hasActiveRule("statement_or_null")) {
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_))
          break;
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (!grammar_scopes_.back().accepts(peek().kind)) break;
      consumeInto(line_);
    }
    const AnnexState prefix = endGrammar(false);
    if (prefix.failed || prefix.interrupted ||
        !prefix.hasActiveRule("statement_or_null")) {
      recordGrammarFallback("invalid Annex A cover assertion header");
      recoverMalformedItem(saved);
      return true;
    }
    grammar_contexts_.push_back({block_stack_.size(), {"statement_or_null"}});
    parseStatement();
    grammar_contexts_.pop_back();
    return true;
  }

  // immediate_assertion_statement ::= simple_immediate_assertion_statement
  // | deferred_immediate_assertion_statement. The local chart handles the
  // shared assert/assume/cover prefix and any #0/final modifier, then the
  // selected Annex A body production parses its own tokens.
  auto parseImmediateAssertionRule() -> bool {
    if (!at(TK::AssertKeyword) && !at(TK::AssumeKeyword) &&
        !at(TK::CoverKeyword)) {
      return false;
    }
    if (at(TK::PropertyKeyword, 1) || at(TK::SequenceKeyword, 1))
      return false;
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"immediate_assertion_statement"});
    while (!at(TK::EndOfFile) &&
           !grammar_scopes_.back().hasActiveRule("action_block") &&
           !grammar_scopes_.back().hasActiveRule("statement_or_null")) {
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_))
          break;
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (!grammar_scopes_.back().accepts(peek().kind)) break;
      consumeInto(line_);
    }
    const AnnexState prefix = endGrammar(false);
    if (prefix.failed || prefix.interrupted ||
        (!prefix.hasActiveRule("action_block") &&
         !prefix.hasActiveRule("statement_or_null"))) {
      recordGrammarFallback("invalid Annex A immediate assertion header");
      recoverMalformedItem(saved);
      return true;
    }
    if (prefix.hasActiveRule("action_block")) {
      parseActionBlockRule();
    } else {
      grammar_contexts_.push_back({block_stack_.size(), {"statement_or_null"}});
      parseStatement();
      grammar_contexts_.pop_back();
    }
    return true;
  }

  // expect_property_statement ::= 'expect' '(' property_spec ')' action_block.
  auto parseExpectPropertyStatementRule() -> bool {
    if (!at(TK::ExpectKeyword)) return false;
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"expect_property_statement"});
    consumeInto(line_);
    if (!at(TK::OpenParenthesis)) {
      static_cast<void>(endGrammar(false));
      recordGrammarFallback("invalid Annex A expect header");
      recoverMalformedItem(saved);
      return true;
    }
    consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                          "property_spec", line_);
    const AnnexState prefix = endGrammar(false);
    if (prefix.failed || prefix.interrupted ||
        !prefix.hasActiveRule("action_block") || line_.tokens.empty() ||
        line_.tokens.back().kind != TK::CloseParenthesis) {
      recordGrammarFallback("incomplete Annex A expect property");
      recoverMalformedItem(saved);
      return true;
    }
    parseActionBlockRule();
    return true;
  }

  // Identifier-led items can become declarations, assignments or
  // instantiations. Consume the common prefix once; list layout starts only
  // while an Annex A instantiation production remains viable.
  auto parseIdentifierItem() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    const auto has_instantiation = [&] {
      if (grammar_scopes_.empty() || grammar_scopes_.back().failed ||
          grammar_scopes_.back().interrupted) {
        return false;
      }
      const auto& grammar = grammar_scopes_.back();
      return grammar.hasViableRule("module_instantiation") ||
             grammar.hasViableRule("interface_instantiation") ||
             grammar.hasViableRule("program_instantiation") ||
             grammar.hasViableRule("checker_instantiation") ||
             grammar.hasViableRule("udp_instantiation") ||
             grammar.hasActiveRule("hierarchical_instance") ||
             grammar.hasActiveRule("udp_instance");
    };
    const bool instantiation_prefix = has_instantiation();
    bool parameter_list_had_directive = false;
    const auto can_layout_instance = [&] {
      return has_instantiation() ||
             (instantiation_prefix && !grammar_scopes_.empty() &&
              (grammar_scopes_.back().interrupted ||
               (grammar_scopes_.back().failed &&
                parameter_list_had_directive)));
    };
    while (at(TK::Directive) && isCompilerDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if (at(TK::Hash) && can_layout_instance() && grammarAllows(TK::Hash)) {
      consumeInto(line_);
      parameter_list_had_directive = parseParenthesizedListInto(line_);
      while (at(TK::Directive) && isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    }
    if (at(TK::Identifier) && can_layout_instance() &&
        grammarAllows(TK::Identifier)) {
      consumeInto(line_);
      if (at(TK::OpenParenthesis) && can_layout_instance() &&
          grammarAllows(TK::OpenParenthesis)) {
        parseParenthesizedListInto(line_);
        while (at(TK::Comma) && grammarAllows(TK::Comma)) {
          consumeInto(line_);
          addLine();
          if (!at(TK::Identifier) || !grammarAllows(TK::Identifier)) break;
          consumeInto(line_);
          if (!at(TK::OpenParenthesis) || !grammarAllows(TK::OpenParenthesis)) {
            break;
          }
          parseParenthesizedListInto(line_);
        }
        if (at(TK::Semicolon) && grammarAllows(TK::Semicolon)) {
          consumeInto(line_);
        }
        if (!grammar_scopes_.empty() && (grammar_scopes_.back().complete() ||
                                         grammar_scopes_.back().interrupted)) {
          addLine();
          return;
        }
      }
    }
    parseGrammarLeaf(true, saved);
  }

  // `ifdef / `define / `include / ... — consume to end of source line
  auto parseDirectiveLine() -> void {
    const bool was_suspended = std::exchange(grammar_suspended_, true);
    // Preserve directives whose spacing or keyword text can affect parsing.
    // Macro definitions can also contain line continuations.
    const auto directive = peek().rawText();
    if (recovery_enabled_ &&
        (directive == "`define" || directive == "`pragma" ||
         directive == "`timescale")) {
      addLine();
      const size_t start = pos_;
      const size_t source_end =
          std::min(tokens_.back().location().offset(), source_.size());
      const size_t raw_begin =
          start == 0 ? 0
                     : std::min(tokens_[start - 1].location().offset() +
                                    tokens_[start - 1].rawText().size(),
                                source_end);

      size_t raw_end = std::min(tokens_[start].location().offset(), source_end);
      while (raw_end < source_end) {
        const size_t newline = source_.find_first_of("\r\n", raw_end);
        if (newline == std::string_view::npos || newline >= source_end) {
          raw_end = source_end;
          break;
        }
        const bool continued =
            newline > raw_end && source_.at(newline - 1) == '\\';
        raw_end = newline + 1;
        if (source_.at(newline) == '\r' && raw_end < source_end &&
            source_.at(raw_end) == '\n') {
          ++raw_end;
        }
        if (!continued) {
          break;
        }
      }

      while (!at(TK::EndOfFile) &&
             tokens_[pos_].location().offset() < raw_end) {
        ++pos_;
      }
      // The printer skips the next token's leading trivia after an opaque
      // line, so include intervening comments and blank lines here.
      raw_end = at(TK::EndOfFile) ? source_end : sourceLineStart(pos_);
      appendOpaqueRange(raw_begin, raw_end);
      attachOpaqueTokens(start, pos_);
      grammar_suspended_ = was_suspended;
      return;
    }

    consumeInto(line_);
    while (pos_ < tokens_.size() && !at(TK::EndOfFile)) {
      if (hasLeadingNewline(peek())) {
        break;
      }
      consumeInto(line_);
    }
    addLine();
    grammar_suspended_ = was_suspended;
  }

  // Macro expansion is absent from the token stream. Preserve one invocation
  // through its semicolon or source line, leaving the enclosing close unread.
  auto parseMacroItem() -> void {
    const bool was_suspended = std::exchange(grammar_suspended_, true);
    int depth = 0;
    bool first = true;
    while (!at(TK::EndOfFile)) {
      if (!first &&
          ((depth == 0 && hasLeadingNewline(peek())) ||
           matchingOpenFrame(peek().kind) || isCompilerDirective(peek()) ||
           (stop_at_conditional_boundary_ &&
            isConditionalBoundaryDirective(peek())))) {
        break;
      }
      const TK kind = peek().kind;
      if (kind == TK::OpenParenthesis || kind == TK::OpenBracket ||
          kind == TK::OpenBrace) {
        ++depth;
      } else if ((kind == TK::CloseParenthesis || kind == TK::CloseBracket ||
                  kind == TK::CloseBrace) &&
                 depth > 0) {
        --depth;
      }
      consumeInto(line_);
      first = false;
      if (kind == TK::Semicolon && depth == 0) break;
    }
    addLine();
    grammar_suspended_ = was_suspended;
  }

  auto parseMacroStatement() -> void {
    beginGrammar(grammarRoots(), true);
    grammar_scopes_.back().interrupted = true;
    recordGrammarFallback("macro expansion unavailable to Annex A");
    parseMacroItem();
    static_cast<void>(endGrammar());
  }

  auto parseConditionalRegion() -> void {
    const Token start = peek();
    ParserState branch_entry = snapshotState();

    parseDirectiveLine();
    branch_entry = snapshotState();
    branch_entry.line = Line{};

    std::vector<ParserState> branch_states;
    bool saw_alternative = false;

    while (!at(TK::EndOfFile)) {
      ParserState branch_start = branch_entry;
      branch_start.pos = pos_;
      branch_start.line = Line{};

      BranchResult branch = parseBranch(branch_start);
      branch_states.push_back(branch.state);
      pos_ = branch.state.pos;
      appendBranchResult(branch);

      restoreState(branch_entry);
      pos_ = branch_states.back().pos;
      line_ = Line{};

      if (isConditionalAlternativeDirective(peek())) {
        saw_alternative = true;
        parseDirectiveLine();
        branch_entry.pos = pos_;
        branch_entry.line = Line{};
        continue;
      }

      if (isConditionalEndDirective(peek())) {
        if (!saw_alternative) {
          ParserState empty_branch = branch_entry;
          empty_branch.pos = pos_;
          empty_branch.line = Line{};
          branch_states.push_back(empty_branch);
        }

        parseDirectiveLine();
        auto joined = joinStates(branch_states);
        if (!joined.has_value()) {
          warnIncompatibleConditional(start);
          joined = branch_states.front();
        }
        joined->pos = pos_;
        joined->line = Line{};
        restoreState(*joined);
        return;
      }

      return;
    }
  }

  // Each top-level comma-separated item in a parenthesized list gets its own
  // UnwrappedLine, so parameters and ports can expand vertically.
  static auto advanceListDepth(ListDepth& depth, TK kind) -> void {
    switch (kind) {
      case TK::OpenParenthesis:
        ++depth.parens;
        break;
      case TK::CloseParenthesis:
        if (depth.parens > 0) --depth.parens;
        break;
      case TK::OpenBracket:
        ++depth.brackets;
        break;
      case TK::CloseBracket:
        if (depth.brackets > 0) --depth.brackets;
        break;
      case TK::ApostropheOpenBrace:
      case TK::OpenBrace:
        ++depth.braces;
        break;
      case TK::CloseBrace:
        if (depth.braces > 0) --depth.braces;
        break;
      default:
        break;
    }
  }

  auto parseParenthesizedListInto(
      Line& line, TK recovery_close = TK::EndOfFile) -> bool {
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    line.tokens.push_back(consume());

    addLine();
    bool had_compiler_directive = false;
    ListDepth depth;

    while (!at(TK::EndOfFile)) {
      had_compiler_directive |= isCompilerDirective(peek());
      if (at(TK::CloseParenthesis) && depth.topLevel()) {
        break;
      }
      if (depth.topLevel() &&
          ((recovery_close != TK::EndOfFile &&
            matchesBlockClose(recovery_close, peek().kind)) ||
           matchingOpenFrame(peek().kind))) {
        break;
      }

      if (depth.topLevel() && isConditionalStartDirective(peek()) &&
          !grammar_scopes_.empty()) {
        bool header_ended = true;
        static_cast<void>(parseAnnexConditional(TK::EndOfFile, header_ended,
                                                indent_level_, &depth));
        continue;
      }

      if (depth.topLevel() && isCompilerDirective(peek()) &&
          (line.tokens.empty() || hasLeadingNewline(peek()))) {
        addLine();
        const bool was_suspended = std::exchange(grammar_suspended_, true);
        consumeInto(line);
        while (pos_ < tokens_.size() && !at(TK::EndOfFile)) {
          if (hasLeadingNewline(peek())) {
            break;
          }
          consumeInto(line);
        }
        addLine();
        grammar_suspended_ = was_suspended;
        continue;
      }

      if (at(TK::Comma) && depth.topLevel()) {
        consumeInto(line);
        addLine();
        continue;
      }

      advanceListDepth(depth, peek().kind);
      consumeInto(line);
    }
    addLine();
    if (at(TK::CloseParenthesis)) {
      line.tokens.push_back(consume());
    } else {
      recordGrammarFallback("unterminated Annex A parenthesized list");
      if (!grammar_scopes_.empty()) grammar_scopes_.back().interrupted = true;
    }
    return had_compiler_directive;
  }

  // module foo #(...) (...); ... endmodule
  auto consumeGrammarHeader(
      TK closeKw, std::initializer_list<std::string_view> boundaryRules,
      std::initializer_list<std::string_view> completedRules = {}) -> void {
    while (!at(TK::EndOfFile) && !at(closeKw) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_)) {
          break;
        }
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (grammar_scopes_.back().failed || grammar_scopes_.back().interrupted ||
          !grammar_scopes_.back().accepts(peek().kind)) {
        recordGrammarFallback("header outside Annex A rule");
        grammar_scopes_.back().interrupted = true;
        while (!at(TK::EndOfFile) && !at(closeKw) && !at(TK::Semicolon) &&
               !(stop_at_conditional_boundary_ &&
                 isConditionalBoundaryDirective(peek()))) {
          consumeInto(line_);
        }
        if (at(TK::Semicolon)) consumeInto(line_);
        addLine();
        return;
      }
      consumeInto(line_);
      const auto& grammar = grammar_scopes_.back();
      const bool boundary =
          std::ranges::any_of(boundaryRules,
                              [&](std::string_view rule) {
                                return grammar.consumedTerminalInRule(
                                    rule, TK::Semicolon);
                              }) ||
          std::ranges::any_of(completedRules, [&](std::string_view rule) {
            return grammar.completedFrom(rule, 0);
          });
      if (boundary) {
        addLine();
        return;
      }
    }
    recordGrammarFallback("incomplete Annex A header");
    addLine();
  }

  auto parseAnnexDelimitedBlock(TK closeKw, std::string_view declarationRule,
                                std::string_view bodyRule,
                                bool hasHeader = true) -> void {
    beginGrammar({declarationRule});
    if (hasHeader) {
      consumeGrammarHeader(closeKw, {declarationRule});
    } else {
      consumeInto(line_);  // specify
      if (!grammar_scopes_.back().consumedTerminalInRule(declarationRule,
                                                         TK::SpecifyKeyword)) {
        recordGrammarFallback("specify header outside Annex A rule");
      }
      addLine();
    }
    const AnnexState header = endGrammar(false);
    const bool global_clocking = declarationRule == "clocking_declaration" &&
                                 header.hasViableProductionStartingWith(
                                     declarationRule, TK::GlobalKeyword);
    if (global_clocking) {
      pushOpenFrame(closeKw);
      ++indent_level_;
      while (isCompilerDirective(peek())) parseDirectiveLine();
      if (!at(closeKw)) {
        recordGrammarFallback("global clocking has no clocking_item body");
        emitOpaque(pos_, findOuterBoundary(pos_));
      }
      if (at(closeKw)) parseOpenFrameClose();
      return;
    }
    parseDelimitedBody(closeKw, bodyRule);
  }

  auto consumeAnnexConditionalToken(TK closeKw, bool& headerEnded,
                                    size_t baseIndent,
                                    ListDepth* listDepth = nullptr) -> bool {
    if (at(TK::Semicolon) &&
        (grammar_scopes_.back().completed("property_spec") ||
         grammar_scopes_.back().completed("sequence_expr"))) {
      const bool suspended = grammar_suspended_;
      grammar_suspended_ = true;
      consumeInto(line_);
      grammar_suspended_ = suspended;
      addLine();
      return true;
    }
    if (grammar_scopes_.back().failed || grammar_scopes_.back().interrupted ||
        !grammar_scopes_.back().accepts(peek().kind)) {
      return false;
    }
    const TK kind = peek().kind;
    if (listDepth && kind == TK::CloseParenthesis && listDepth->topLevel()) {
      return false;
    }
    if (kind == closeKw) {
      addLine();
      if (indent_level_ > baseIndent) --indent_level_;
    }
    const bool list_separator =
        listDepth && kind == TK::Comma && listDepth->topLevel();
    if (listDepth) advanceListDepth(*listDepth, kind);
    consumeInto(line_);
    if (list_separator) {
      addLine();
    } else if (kind == TK::Semicolon) {
      addLine();
      if (!headerEnded) {
        headerEnded = true;
        ++indent_level_;
      }
    }
    return !grammar_scopes_.back().failed;
  }

  // Conditional compilation is outside Annex A. Each branch advances copies
  // of every active chart as its tokens are emitted. A compatible continuation
  // resumes after endif without replaying any branch tokens.
  auto parseAnnexConditional(TK closeKw, bool& headerEnded, size_t baseIndent,
                             ListDepth* listDepth = nullptr) -> bool {
    addLine();
    parseDirectiveLine();  // ifdef / ifndef
    const auto entry = grammar_scopes_;
    const bool entry_header_ended = headerEnded;
    const size_t entry_indent = indent_level_;
    const ListDepth entry_depth = listDepth ? *listDepth : ListDepth{};
    struct Continuation {
      std::vector<AnnexState> grammars;
      bool header_ended;
      size_t indent;
      ListDepth depth;
    };
    std::vector<Continuation> branches;
    bool has_else = false;
    while (!at(TK::EndOfFile)) {
      grammar_scopes_ = entry;
      headerEnded = entry_header_ended;
      indent_level_ = entry_indent;
      if (listDepth) *listDepth = entry_depth;
      while (!at(TK::EndOfFile) && !isConditionalBoundaryDirective(peek())) {
        if (isConditionalStartDirective(peek())) {
          if (!parseAnnexConditional(closeKw, headerEnded, baseIndent,
                                     listDepth)) {
            return false;
          }
        } else if (isCompilerDirective(peek())) {
          addLine();
          parseDirectiveLine();
        } else if (!consumeAnnexConditionalToken(closeKw, headerEnded,
                                                 baseIndent, listDepth)) {
          return false;
        }
      }
      addLine();
      branches.push_back({grammar_scopes_, headerEnded, indent_level_,
                          listDepth ? *listDepth : ListDepth{}});
      if (!isConditionalAlternativeDirective(peek())) break;
      has_else |= peek().rawText() == "`else";
      parseDirectiveLine();
    }
    if (!at(TK::Directive) || !isConditionalEndDirective(peek())) {
      recordGrammarFallback("unterminated conditional Annex A declaration");
      return false;
    }
    parseDirectiveLine();  // endif
    if (!has_else) {
      branches.push_back(
          {entry, entry_header_ended, entry_indent, entry_depth});
    }
    if (branches.empty()) return false;
    const auto& joined = branches.front();
    for (const auto& branch : branches) {
      bool same_grammar = joined.grammars.size() == branch.grammars.size();
      for (size_t i = 0; same_grammar && i < joined.grammars.size(); ++i) {
        const auto& left = joined.grammars[i];
        const auto& right = branch.grammars[i];
        same_grammar = left.roots == right.roots &&
                       left.failed == right.failed &&
                       left.interrupted == right.interrupted;
      }
      if (!same_grammar || joined.header_ended != branch.header_ended ||
          joined.indent != branch.indent || joined.depth != branch.depth) {
        recordGrammarFallback("incompatible conditional Annex A branches");
        return false;
      }
    }
    grammar_scopes_ = joined.grammars;
    for (size_t branch = 1; branch < branches.size(); ++branch) {
      for (size_t i = 0; i < grammar_scopes_.size(); ++i) {
        grammar_scopes_[i].addContinuation(branches[branch].grammars[i]);
      }
    }
    headerEnded = joined.header_ended;
    indent_level_ = joined.indent;
    if (listDepth) *listDepth = joined.depth;
    return true;
  }

  // Annex A gives property and sequence declarations a header, repeated local
  // declarations, and one final expression. Advance both possible body rules
  // together because a user-defined data type and an expression may both
  // start with an identifier. A completed local declaration gets a fresh
  // chart; the final expression retains its chart through the closing token.
  auto parseAnnexWholeBlock(TK closeKw,
                            std::string_view declarationRule) -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({declarationRule});
    consumeGrammarHeader(closeKw, {declarationRule});
    const AnnexState header = endGrammar(false);
    const std::string_view expression_rule =
        closeKw == TK::EndPropertyKeyword ? "property_spec" : "sequence_expr";
    const std::vector<std::string_view> body_rules = {
        "assertion_variable_declaration", expression_rule};
    bool complete = !header.failed && !header.interrupted;
    const bool body_started = complete;
    if (complete) {
      ++indent_level_;
      beginGrammar(body_rules);
    }
    while (!at(TK::EndOfFile) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek())) &&
           complete) {
      const auto& grammar = grammar_scopes_.back();
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        complete =
            parseAnnexConditional(closeKw, header_ended, saved.indent_level);
        continue;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (grammar.completed(expression_rule) &&
          (at(TK::Semicolon) || at(closeKw))) {
        break;
      }
      if (grammar.completed("assertion_variable_declaration") &&
          !grammar.completed(expression_rule)) {
        static_cast<void>(endGrammar());
        beginGrammar(body_rules);
        continue;
      }
      if (grammar.failed || grammar.interrupted ||
          !grammar.accepts(peek().kind)) {
        complete = false;
        break;
      }
      const TK kind = peek().kind;
      consumeInto(line_);
      if (kind == TK::Semicolon) addLine();
    }
    if (complete) {
      complete = grammar_scopes_.back().completed(expression_rule) &&
                 (at(TK::Semicolon) || at(closeKw));
      static_cast<void>(endGrammar(false));
    } else if (body_started) {
      static_cast<void>(endGrammar(false));
    }
    if (complete) {
      if (at(TK::Semicolon)) {
        consumeInto(line_);
        addLine();
      }
      addLine();
      pushOpenFrame(closeKw);
      parseOpenFrameClose();
      return;
    }
    recordGrammarFallback("malformed Annex A declaration");
    lines_.resize(saved.output_size);
    line_ = saved.line;
    preserved_source_end_ = saved.preserved_source_end;
    indent_level_ = saved.indent_level;
    pos_ = saved.pos;
    parseOpaqueBlock(closeKw);
  }

  auto parseAnnexItem(std::vector<std::string_view> rules,
                      bool stop_at_complete_semicolon = false) -> AnnexState {
    beginGrammar(std::move(rules));
    parseGrammarLeaf(false, {}, stop_at_complete_semicolon);
    return endGrammar();
  }

  // Some parent productions append ';' to a child declaration. Keep the
  // child's final line open, then consume the parent's required terminal.
  auto parseAnnexSemicolonItem(std::string_view child_rule) -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({child_rule});
    parseGrammarLeaf(false, {}, false, true);
    const AnnexState child = endGrammar();
    if (child.failed || child.interrupted || !child.complete()) return;
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A parent semicolon");
      recoverMalformedItem(saved);
      return;
    }
    consumeInto(line_);
    addLine();
  }

  auto parseConstraintBlock(std::vector<std::string_view> roots = {
                                "constraint_declaration",
                                "extern_constraint_declaration"}) -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar(std::move(roots));
    bool opened = false;
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (!grammar_scopes_.back().accepts(peek().kind)) break;
      consumeInto(line_);
      if (grammar_scopes_.back().completed("extern_constraint_declaration")) {
        addLine();
        static_cast<void>(endGrammar());
        return;
      }
      if (grammar_scopes_.back().consumedTerminalInRule("constraint_block",
                                                        TK::OpenBrace)) {
        addLine();
        opened = true;
        break;
      }
    }
    const AnnexState header = endGrammar(false);
    if (!opened || header.failed || header.interrupted) {
      recordGrammarFallback("malformed Annex A constraint header");
      lines_.resize(saved.output_size);
      line_ = saved.line;
      preserved_source_end_ = saved.preserved_source_end;
      indent_level_ = saved.indent_level;
      pos_ = saved.pos;
      emitOpaque(pos_, findOuterBoundary(pos_));
      return;
    }

    const TK outer_close =
        block_stack_.empty() ? TK::EndOfFile : block_stack_.back().close_kind;
    pushOpenFrame(TK::CloseBrace);
    block_stack_.back().grammar_body = "constraint_block_item";
    ++indent_level_;
    while (!at(TK::CloseBrace) && !at(TK::EndOfFile) && !at(outer_close) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
      parseStatement();
    }
    if (at(TK::CloseBrace)) {
      parseOpenFrameClose();
    } else {
      recordGrammarFallback("incomplete Annex A constraint block");
      block_stack_.pop_back();
      if (indent_level_ > 0) --indent_level_;
    }
  }

  auto parseConfigBlock() -> void {
    beginGrammar({"config_declaration"});
    consumeGrammarHeader(TK::EndConfigKeyword, {"config_declaration"});
    static_cast<void>(endGrammar(false));
    pushOpenFrame(TK::EndConfigKeyword);
    block_stack_.back().grammar_body = "config_body";
    ++indent_level_;
    parseLevel(TK::EndConfigKeyword);
    if (block_stack_.empty() ||
        block_stack_.back().close_kind != TK::EndConfigKeyword) {
      recordGrammarFallback("config body lost its closing boundary");
      return;
    }
    if (!block_stack_.back().statement_phase) {
      recordGrammarFallback("config requires design_statement");
    }
    if (at(TK::EndConfigKeyword)) {
      parseOpenFrameClose();
    } else {
      recordGrammarFallback("incomplete config declaration");
    }
  }

  auto parseConfigItem() -> void {
    const bool before_design = !block_stack_.back().statement_phase;
    if (before_design && at(TK::LocalParamKeyword)) {
      beginGrammar({"local_parameter_declaration"});
      while (!at(TK::EndOfFile) && !at(TK::Semicolon) &&
             !matchingOpenFrame(peek().kind) &&
             grammar_scopes_.back().accepts(peek().kind)) {
        consumeInto(line_);
      }
      const bool complete = grammar_scopes_.back().complete();
      static_cast<void>(endGrammar());
      if (complete && at(TK::Semicolon)) {
        consumeInto(line_);  // required by config_declaration
        addLine();
      } else {
        recordGrammarFallback("malformed config local parameter");
        consumeUntilSemi();
      }
      return;
    }
    if (before_design && at(TK::DesignKeyword)) {
      const AnnexState item = parseAnnexItem({"design_statement"});
      block_stack_.back().statement_phase = item.complete();
      return;
    }
    static_cast<void>(parseAnnexItem(grammarRoots()));
  }

  auto parsePrimitiveBlock() -> void {
    beginGrammar({"udp_declaration"});
    consumeGrammarHeader(
        TK::EndPrimitiveKeyword, {},
        {"udp_nonansi_declaration", "udp_ansi_declaration", "udp_declaration"});
    const AnnexState header = endGrammar(false);
    if (header.complete()) return;  // extern udp_declaration has no body
    const bool nonansi = header.completedFrom("udp_nonansi_declaration", 0);
    const bool ansi = header.completedFrom("udp_ansi_declaration", 0);
    pushOpenFrame(TK::EndPrimitiveKeyword);
    block_stack_.back().grammar_body = "udp_body";
    block_stack_.back().udp_nonansi_header = nonansi;
    block_stack_.back().udp_ansi_header = ansi;
    ++indent_level_;
    parseLevel(TK::EndPrimitiveKeyword);
    if (block_stack_.empty() ||
        block_stack_.back().close_kind != TK::EndPrimitiveKeyword) {
      recordGrammarFallback("UDP body lost its closing boundary");
      return;
    }
    const auto& udp = block_stack_.back();
    if ((udp.udp_nonansi_header && !udp.udp_port_on_all_paths) ||
        (udp.udp_ansi_header && udp.udp_port_on_any_path)) {
      recordGrammarFallback("UDP port declarations do not match header");
    }
    if (!udp.statement_phase) {
      recordGrammarFallback("UDP declaration requires udp_body");
    }
    if (at(TK::EndPrimitiveKeyword)) {
      parseOpenFrameClose();
    } else if (!(stop_at_conditional_boundary_ &&
                 isConditionalBoundaryDirective(peek()))) {
      recordGrammarFallback("incomplete UDP declaration");
    }
  }

  auto parseUdpBodyItem() -> void {
    const auto& body = block_stack_.back();
    const bool before_table = !body.statement_phase;
    if (before_table && !body.udp_ansi_header && !body.udp_initial_seen &&
        (at(TK::InputKeyword) || at(TK::OutputKeyword) ||
         at(TK::RegKeyword))) {
      const AnnexState item = parseAnnexItem({"udp_port_declaration"});
      if (item.complete()) {
        auto& udp = block_stack_.back();
        udp.udp_port_on_all_paths = true;
        udp.udp_port_on_any_path = true;
      }
      return;
    }
    if (before_table && !body.udp_initial_seen && at(TK::InitialKeyword)) {
      const AnnexState item = parseAnnexItem({"udp_initial_statement"});
      block_stack_.back().udp_initial_seen = item.complete();
      return;
    }
    if (before_table && at(TK::TableKeyword)) {
      consumeInto(line_);  // table
      addLine();
      const bool sequential = block_stack_.back().udp_initial_seen;
      pushOpenFrame(TK::EndTableKeyword);
      block_stack_.back().grammar_body = "udp_table_entry";
      block_stack_.back().udp_sequential = sequential;
      ++indent_level_;
      while (!at(TK::EndTableKeyword) && !at(TK::EndPrimitiveKeyword) &&
             !at(TK::EndOfFile) &&
             !(stop_at_conditional_boundary_ &&
               isConditionalBoundaryDirective(peek()))) {
        parseStatement();
      }
      if (!block_stack_.back().udp_has_entry) {
        recordGrammarFallback("UDP table requires an entry");
      }
      const bool table_closed = at(TK::EndTableKeyword);
      if (at(TK::EndTableKeyword)) {
        parseOpenFrameClose();
      } else {
        recordGrammarFallback("incomplete UDP table");
        block_stack_.pop_back();
        if (indent_level_ > 0) --indent_level_;
      }
      block_stack_.back().statement_phase = table_closed;
      return;
    }
    static_cast<void>(parseAnnexItem(grammarRoots()));
  }

  auto parseStructuralBlock(TK closeKw) -> void {
    std::vector<std::string_view> roots;
    std::string_view body_rule;
    switch (closeKw) {
      case TK::EndModuleKeyword:
        roots = {"module_ansi_header", "module_nonansi_header"};
        body_rule = "module_item";
        break;
      case TK::EndInterfaceKeyword:
        roots = {"interface_ansi_header", "interface_nonansi_header"};
        body_rule = "interface_item";
        break;
      case TK::EndProgramKeyword:
        roots = {"program_ansi_header", "program_nonansi_header"};
        body_rule = "program_item";
        break;
      case TK::EndPackageKeyword:
        roots = {"package_declaration"};
        body_rule = "package_item";
        break;
      default:
        break;
    }
    if (!roots.empty()) beginGrammar(roots);
    if (closeKw == TK::EndPackageKeyword) {
      // package_declaration includes its body; the first grammar-accepted
      // semicolon separates its header from package_item repetitions.
      consumeGrammarHeader(closeKw, {"package_declaration"});
    } else {
      // The header chart ends the header, including any package imports. A
      // semicolon inside an import cannot be mistaken for the body boundary.
      while (!at(closeKw) && !at(TK::EndOfFile) &&
             !grammar_scopes_.back().complete()) {
        if (isConditionalStartDirective(peek())) {
          bool header_ended = true;
          if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                     indent_level_)) {
            break;
          }
          continue;
        }
        if (isCompilerDirective(peek())) {
          addLine();
          parseDirectiveLine();
          continue;
        }
        if (grammar_scopes_.back().interrupted ||
            grammar_scopes_.back().failed) {
          // An unavailable macro can interrupt the Annex A header before the
          // port list. Preserve that list's formatter layout while looking
          // for the header's semicolon; the grammar fallback was diagnosed at
          // the interruption.
          if (at(TK::OpenParenthesis)) {
            parseParenthesizedListInto(line_, closeKw);
          } else {
            const TK kind = peek().kind;
            consumeInto(line_);
            if (kind == TK::Semicolon) break;
          }
          continue;
        }
        if (!grammar_scopes_.back().accepts(peek().kind)) break;
        if (at(TK::Hash)) {
          consumeInto(line_);
          static_cast<void>(consumeBalancedInto(
              TK::OpenParenthesis, TK::CloseParenthesis, line_, closeKw));
        } else if (at(TK::OpenParenthesis)) {
          // Port lists are layout choices over the same grammar consumption.
          parseParenthesizedListInto(line_, closeKw);
        } else {
          consumeInto(line_);
        }
      }
      if ((grammar_scopes_.back().interrupted ||
           grammar_scopes_.back().failed) &&
          !line_.tokens.empty() && line_.tokens.back().kind != TK::Semicolon) {
        // A macro or malformed token interrupted the header chart. Preserve
        // the rest of this header through its next source semicolon.
        consumeUntilSemi();
      }
    }
    addLine();
    if (closeKw == TK::EndPackageKeyword) {
      // package_declaration has no separate header rule. Its viable prefix
      // validates the header through the first semicolon; each package_item
      // gets its own chart so a large package has bounded grammar state.
      static_cast<void>(endGrammar(false));
      parseDelimitedBody(closeKw, body_rule);
      return;
    }
    const AnnexState header = endGrammar();
    if (closeKw == TK::EndModuleKeyword &&
        header.completed("module_ansi_header") &&
        !header.completed("module_nonansi_header")) {
      body_rule = "non_port_module_item";
    } else if (closeKw == TK::EndInterfaceKeyword &&
               header.completed("interface_ansi_header") &&
               !header.completed("interface_nonansi_header")) {
      body_rule = "non_port_interface_item";
    } else if (closeKw == TK::EndProgramKeyword &&
               header.completed("program_ansi_header") &&
               !header.completed("program_nonansi_header")) {
      body_rule = "non_port_program_item";
    }
    parseDelimitedBody(closeKw, body_rule);
  }

  // class / function / task ... endclass / endfunction / endtask
  auto parseNamedBlock(TK closeKw) -> void {
    std::vector<std::string_view> roots;
    std::string_view body_rule;
    switch (closeKw) {
      case TK::EndClassKeyword:
        roots = {"class_declaration", "interface_class_declaration"};
        break;
      case TK::EndFunctionKeyword:
        roots = {"function_declaration"};
        break;
      case TK::EndTaskKeyword:
        roots = {"task_declaration"};
        break;
      default:
        break;
    }
    if (!roots.empty()) beginGrammar(roots);
    switch (closeKw) {
      case TK::EndClassKeyword:
        consumeGrammarHeader(
            closeKw, {"class_declaration", "interface_class_declaration"});
        break;
      case TK::EndFunctionKeyword:
        consumeGrammarHeader(closeKw, {"function_body_declaration"});
        break;
      case TK::EndTaskKeyword:
        consumeGrammarHeader(closeKw, {"task_body_declaration"});
        break;
      default:
        break;
    }
    // The declaration grammar validates the viable header prefix. Its body
    // items are parsed with their Annex A rules one at a time, avoiding a
    // whole-class or whole-function chart for large declarations.
    if (!roots.empty()) {
      const AnnexState header = endGrammar(false);
      if (closeKw == TK::EndClassKeyword) {
        body_rule = header.hasViableRule("interface_class_declaration")
                        ? "interface_class_item"
                        : "class_item";
      }
    }
    parseDelimitedBody(closeKw, body_rule);
  }

  // generate ... endgenerate
  auto parseSimpleBlock(TK closeKw) -> void {
    beginGrammar({"generate_region"});
    consumeInto(line_);
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted ||
        !header.hasViableRule("generate_region")) {
      recordGrammarFallback("invalid Annex A generate region header");
    }
    addLine();

    parseDelimitedBody(closeKw);
  }

  // begin [:label] ... end [:label]
  auto parseBeginEnd(TK closeKw) -> void {
    beginGrammar({"seq_block"});
    consumeInto(line_);  // begin
    consumeLabel();
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted ||
        !header.hasViableRule("seq_block")) {
      recordGrammarFallback("invalid Annex A sequential block header");
    }
    addLine();

    parseDelimitedBody(closeKw);
  }

  // fork ... join / join_any / join_none
  auto parseFork(TK closeKw) -> void {
    beginGrammar({"par_block"});
    consumeInto(line_);
    consumeLabel();
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted ||
        !header.hasViableRule("par_block")) {
      recordGrammarFallback("invalid Annex A parallel block header");
    }
    addLine();
    parseDelimitedBody(closeKw);
  }

  // always / always_comb / always_ff / always_latch / initial / final
  auto parseProceduralBlock() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"always_construct", "initial_construct", "final_construct"});
    consumeInto(line_);  // keyword
    bool has_delay_control = false;
    bool has_event_control = false;
    if (at(TK::Hash)) {
      has_delay_control = true;
      if (!consumeAnnexRule("delay_control", line_)) {
        static_cast<void>(endGrammar(false));
        recoverMalformedItem(saved);
        return;
      }
    }
    if (at(TK::At)) {
      has_event_control = true;
      if (!consumeAnnexRule("event_control", line_)) {
        static_cast<void>(endGrammar(false));
        recoverMalformedItem(saved);
        return;
      }
    }
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted) {
      recoverMalformedItem(saved);
      return;
    }
    std::vector<std::string_view> body_roots;
    if (has_delay_control || has_event_control ||
        header.hasViableRule("initial_construct")) {
      body_roots = {"statement_or_null"};
    } else if (header.hasViableRule("final_construct")) {
      body_roots = {"function_statement"};
    } else if (header.hasViableRule("always_construct")) {
      body_roots = {"statement"};
    } else {
      recordGrammarFallback("procedural body outside Annex A rule");
      recoverMalformedItem(saved);
      return;
    }
    const TK next = peek().kind;
    constexpr std::string_view compound_rules[] = {
        "seq_block", "par_block", "conditional_statement", "case_statement",
        "loop_statement"};
    const bool compound_statement =
        std::ranges::any_of(compound_rules, [&](std::string_view rule) {
          return header.hasActiveRule(rule) && annexCanStart(rule, next);
        });
    if (has_delay_control && !compound_statement) {
      beginGrammar(body_roots);
      parseGrammarLeaf();
      static_cast<void>(endGrammar());
      return;
    }
    addLine();

    parseIndentedStatement(std::move(body_roots));
  }

  // conditional_statement and if_generate_construct from Annex A.
  auto parseIf(bool generate) -> void {
    const std::string_view condition_rule =
        generate ? "constant_expression" : "cond_predicate";
    const std::vector<std::string_view> body_roots = {
        generate ? "generate_block" : "statement_or_null"};
    while (at(TK::IfKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);
      if (!at(TK::OpenParenthesis)) {
        recordGrammarFallback("if requires '(' in Annex A");
        recoverMalformedItem(saved);
        return;
      }
      consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                            condition_rule, line_);
      if (line_.tokens.empty() ||
          line_.tokens.back().kind != TK::CloseParenthesis) {
        recordGrammarFallback("incomplete Annex A if condition");
        recoverMalformedItem(saved);
        return;
      }
      addLine();

      parseIndentedStatement(body_roots);
      if (!at(TK::ElseKeyword)) return;
      consumeInto(line_);
      if (generate || !at(TK::IfKeyword)) {
        addLine();
        parseIndentedStatement(body_roots);
        return;
      }
      // The procedural production repeats `else if (...) statement_or_null`.
      // Keep `else if` together while calling the same rule for its body.
    }
  }

  // case_statement, randcase_statement and case_generate_construct.
  auto parseCase(bool generate) -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    const bool randcase = at(TK::RandCaseKeyword);
    consumeInto(line_);  // case / casex / casez / randcase
    std::string_view body_rule = randcase ? "randcase_item"
                                      : generate ? "case_generate_item"
                                                 : "case_item";
    if (!randcase) {
      if (!at(TK::OpenParenthesis)) {
        recordGrammarFallback("case requires '(' in Annex A");
        recoverMalformedItem(saved);
        return;
      }
      consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                            generate ? "constant_expression" : "case_expression",
                            line_);
      if (line_.tokens.empty() ||
          line_.tokens.back().kind != TK::CloseParenthesis) {
        recordGrammarFallback("incomplete Annex A case expression");
        recoverMalformedItem(saved);
        return;
      }
    }
    if (!randcase && !generate &&
        (at(TK::InsideKeyword) || at(TK::MatchesKeyword))) {
      body_rule =
          at(TK::InsideKeyword) ? "case_inside_item" : "case_pattern_item";
      consumeInto(line_);
    }
    addLine();

    pushOpenFrame(TK::EndCaseKeyword);
    block_stack_.back().grammar_body = body_rule;
    ++indent_level_;
    size_t item_count = 0;
    bool conditional_items = false;
    while (!at(TK::EndCaseKeyword) && !at(TK::EndOfFile)) {
      if (stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(peek())) {
        return;
      }
      if (at(TK::Directive)) {
        conditional_items |= isConditionalStartDirective(peek());
        parseStatement();
      } else {
        parseStatement();
        ++item_count;
      }
    }

    if (at(TK::EndCaseKeyword)) {
      if (item_count == 0 && !conditional_items) {
        recordGrammarFallback("case statement requires an Annex A item");
      }
      parseOpenFrameClose();
    }
  }

  // randsequence_statement ::= randsequence ( [ identifier ] )
  // rs_production { rs_production } endsequence.
  auto parseRandsequenceStatement() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"randsequence_statement"});
    consumeInto(line_);
    if (!at(TK::OpenParenthesis) ||
        !consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_,
                             block_stack_.empty()
                                 ? TK::EndOfFile
                                 : block_stack_.back().close_kind)) {
      static_cast<void>(endGrammar(false));
      recordGrammarFallback("invalid Annex A randsequence header");
      recoverMalformedItem(saved);
      return;
    }
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted ||
        !header.hasViableRule("randsequence_statement")) {
      recordGrammarFallback("invalid Annex A randsequence header");
      recoverMalformedItem(saved);
      return;
    }
    addLine();
    parseDelimitedBody(TK::EndSequenceKeyword, "rs_production");
  }

  auto parseCaseItem() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    const std::string_view item_rule = block_stack_.back().grammar_body;
    beginGrammar({item_rule});
    const bool default_item = at(TK::DefaultKeyword);
    bool colon_seen = false;
    if (default_item) {
      consumeInto(line_);
      if (at(TK::Colon)) {
        consumeInto(line_);
        colon_seen = true;
      }
    } else {
      while (!at(TK::EndOfFile) && !at(TK::EndCaseKeyword) &&
             !(at(TK::Colon) &&
               (grammar_scopes_.back().failed ||
                grammar_scopes_.back().expectsRootTerminal(TK::Colon)))) {
        if (stop_at_conditional_boundary_ &&
            isConditionalBoundaryDirective(peek())) {
          break;
        }
        if (isConditionalStartDirective(peek())) {
          bool header_ended = true;
          if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                     indent_level_)) {
            break;
          }
          continue;
        }
        if (isCompilerDirective(peek())) {
          addLine();
          parseDirectiveLine();
          continue;
        }
        if (at(TK::Directive)) break;
        consumeInto(line_);
      }
      if (at(TK::Colon)) {
        consumeInto(line_);
        colon_seen = true;
      }
    }
    const AnnexState header = endGrammar(false);
    colon_seen |= header.consumedTerminalInRule(item_rule, TK::Colon);
    if ((!default_item && !colon_seen) || header.failed || header.interrupted ||
        !header.hasViableRule(item_rule)) {
      recordGrammarFallback("invalid Annex A case item header");
      recoverMalformedItem(saved);
      return;
    }
    addLine();

    parseIndentedStatement(
        item_rule == "case_generate_item"
            ? std::vector<std::string_view>{"generate_block"}
            : std::vector<std::string_view>{"statement_or_null"});
  }

  // loop_statement and loop_generate_construct from Annex A.
  auto parseLoop(bool generate) -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    if (at(TK::DoKeyword)) {
      consumeInto(line_);
      addLine();
      parseIndentedStatement({"statement_or_null"});
      if (!at(TK::WhileKeyword)) {
        recordGrammarFallback("do statement requires Annex A while tail");
        return;
      }
      consumeInto(line_);
      consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                            "expression", line_);
      if (at(TK::Semicolon)) {
        consumeInto(line_);
      } else {
        recordGrammarFallback("do while requires ';' in Annex A");
      }
      addLine();
      return;
    }
    const TK loop_kind = peek().kind;
    const bool foreach = loop_kind == TK::ForeachKeyword;
    if (foreach) beginGrammar({"loop_statement"});
    consumeInto(line_);
    if (loop_kind == TK::ForKeyword) {
      if (!consumeForHeader(line_, generate)) {
        recoverMalformedItem(saved);
        return;
      }
    } else if (loop_kind == TK::WhileKeyword ||
               loop_kind == TK::RepeatKeyword) {
      consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                            "expression", line_);
      if (line_.tokens.empty() ||
          line_.tokens.back().kind != TK::CloseParenthesis) {
        recordGrammarFallback("incomplete Annex A loop header");
        recoverMalformedItem(saved);
        return;
      }
    } else if (foreach) {
      if (!consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_,
                               block_stack_.empty()
                                   ? TK::EndOfFile
                                   : block_stack_.back().close_kind)) {
        static_cast<void>(endGrammar(false));
        recoverMalformedItem(saved);
        return;
      }
      const AnnexState header = endGrammar(false);
      if (header.failed || header.interrupted ||
          !header.hasViableRule("loop_statement") ||
          !header.consumedTerminalInRule("loop_statement",
                                         TK::CloseParenthesis)) {
        recordGrammarFallback("incomplete Annex A foreach header");
        recoverMalformedItem(saved);
        return;
      }
    }
    if (!generate && at(TK::At)) {
      if (!consumeAnnexRule("event_control", line_)) {
        recoverMalformedItem(saved);
        return;
      }
      if (at(TK::BeginKeyword)) {
        consumeInto(line_);
        consumeLabel();
        addLine();
        parseDelimitedBody(TK::EndKeyword);
        return;
      }
    }
    addLine();

    parseIndentedStatement(
        generate ? std::vector<std::string_view>{"generate_block"}
        : loop_kind == TK::ForeachKeyword
            ? std::vector<std::string_view>{"statement"}
            : std::vector<std::string_view>{"statement_or_null"});
  }

  // NOLINTEND(misc-no-recursion)
};

}  // namespace

[[nodiscard]] auto TreeUnwrapper::unwrap() const
    -> std::vector<UnwrappedLine<slang::parsing::Token>> {
  return unwrapWithDiagnostics().lines;
}

[[nodiscard]] auto TreeUnwrapper::unwrapWithDiagnostics() const
    -> UnwrapResult {
  SVParser parser(tokens, style.get(), original_source);
  auto result = parser.parse();
  size_t output_index = 0;
  bool preserved = true;
  for (const auto& line : result.lines) {
    for (const auto& token : line.tokens) {
      if (output_index >= tokens.size() ||
          token.kind != tokens[output_index].kind ||
          token.rawText() != tokens[output_index].rawText() ||
          token.location() != tokens[output_index].location()) {
        preserved = false;
      }
      ++output_index;
    }
  }
  if (output_index != tokens.size()) preserved = false;
  if (!preserved) {
    result.lines.clear();
    Line original;
    original.tokens.assign(tokens.begin(), tokens.end());
    original.raw_text = std::string(original_source);
    original.is_opaque = !original_source.empty();
    result.lines.push_back(std::move(original));
    if (!tokens.empty()) {
      result.warnings.push_back(
          {.location = tokens.front().location(),
           .code = "token-conservation-fallback",
           .message = "parser recovery did not conserve tokens; original "
                      "source preserved"});
    }
  }
  return result;
}

}  // namespace format
