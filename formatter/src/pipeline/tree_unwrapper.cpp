#include "pipeline/tree_unwrapper.h"

#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <gsl/span>
#include <initializer_list>
#include <limits>
#include <optional>
#include <span>
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

constexpr int kAnnexCompleteSymbol = -32768;
constexpr size_t kAnnexChartItemLimit = 2'000'000;

#include "annex_a/table.inc"

// The table records token names from the slang revision used by the Annex A
// importer. Resolve names because token enum values differ across revisions.
[[nodiscard]] auto annexTerminal(TK kind) -> int {
  static const auto names = [] {
    std::unordered_map<std::string_view, int> result;
    for (size_t i = 0; i < std::size(kTokenNames); ++i) {
      result.emplace(kTokenNames.at(i), static_cast<int>(i));
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
      result.emplace(kRuleNames.at(i), static_cast<int>(i));
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
          const int symbol = kSymbols.at(production.offset + i);
          if (symbol < 0) {
            changed |=
                result.terminals.at(production.left).insert(-symbol - 1).second;
            all_nullable = false;
            break;
          }
          for (const int terminal : result.terminals.at(symbol)) {
            changed |=
                result.terminals.at(production.left).insert(terminal).second;
          }
          if (!result.nullable.at(symbol)) {
            all_nullable = false;
            break;
          }
        }
        if (all_nullable && !result.nullable.at(production.left)) {
          result.nullable.at(production.left) = true;
          changed = true;
        }
      }
    }
    return result;
  }();
  const int rule = annexRule(name);
  const int terminal = annexTerminal(kind);
  return rule >= 0 && terminal >= 0 &&
         sets.terminals.at(static_cast<size_t>(rule)).contains(terminal);
}

[[nodiscard]] auto annexCanStartAny(
    std::initializer_list<std::string_view> rules, TK kind) -> bool {
  return std::ranges::any_of(rules, [kind](std::string_view rule) {
    return annexCanStart(rule, kind);
  });
}

// The optional super.new part has an imported helper production. Retain it
// when a directive or macro interrupts the constructor call itself.
[[nodiscard]] auto annexConstructorSuperRule() -> std::string_view {
  static const std::string_view rule = []() -> std::string_view {
    const int constructor = annexRule("class_constructor_declaration");
    const int super = annexTerminal(TK::SuperKeyword);
    if (constructor < 0 || super < 0) {
      return {};
    }
    for (const auto& parent : kProductions) {
      if (parent.left != constructor) {
        continue;
      }
      for (size_t i = 0; i < parent.count; ++i) {
        const int child = kSymbols.at(parent.offset + i);
        if (child < 0) {
          continue;
        }
        for (const auto& production : kProductions) {
          if (production.left == child && production.count > 0 &&
              kSymbols.at(production.offset) == -super - 1) {
            return kRuleNames.at(child);
          }
        }
      }
    }
    return {};
  }();
  return rule;
}

struct AnnexItem {
  uint16_t production;
  uint16_t dot;
  size_t origin;
  auto operator==(const AnnexItem&) const -> bool = default;
};

struct AnnexItemHash {
  auto operator()(AnnexItem item) const -> size_t {
    constexpr size_t kMix = 0x9e3779b9U;
    constexpr unsigned kShift = 6;
    size_t hash = item.origin;
    hash ^= static_cast<size_t>(item.production) + kMix + (hash << kShift) +
            (hash >> 2U);
    hash ^=
        static_cast<size_t>(item.dot) + kMix + (hash << kShift) + (hash >> 2U);
    return hash;
  }
};

[[nodiscard]] auto annexNext(AnnexItem item) -> int {
  const auto& production = kProductions.at(item.production);
  return item.dot < production.count ? kSymbols.at(production.offset + item.dot)
                                     : kAnnexCompleteSymbol;
}

// Some Annex A lexical terminals share slang token kinds with other spellings.
// Check slang's source lexeme when the chart scans each such terminal.
[[nodiscard]] auto annexLexemeMatches(AnnexItem item, Token token) -> bool {
  static const int output = annexRule("@lexer_output_symbol");
  static const int level = annexRule("@lexer_level_symbol");
  static const int edge = annexRule("@lexer_edge_symbol");
  static const int finish_number = annexRule("finish_number");
  static const int severity = annexRule("severity_system_task");
  static const int fatal_severity_suffix = [] {
    for (const auto& production : kProductions) {
      if (production.left != severity || production.count < 2) {
        continue;
      }
      const int suffix = kSymbols.at(production.offset + 1);
      for (const auto& child : kProductions) {
        if (child.left != suffix) {
          continue;
        }
        const auto symbols =
            std::span(kSymbols).subspan(child.offset, child.count);
        if (std::ranges::find(symbols, finish_number) != symbols.end()) {
          return suffix;
        }
      }
    }
    return -1;
  }();
  static const int edge_descriptor = annexRule("@lexer_edge_descriptor");
  static const int x_digit = annexRule("@lexer_x_digit");
  static const int z_digit = annexRule("@lexer_z_digit");
  static const int binary_number = annexRule("binary_number");
  static const int octal_number = annexRule("octal_number");
  static const int hex_number = annexRule("hex_number");
  const int rule = kProductions.at(item.production).left;
  const std::string_view lexeme = token.rawText();
  const std::string_view rule_name = kRuleNames.at(rule);
  const auto matches_base = [&](char lower, char upper) {
    return lexeme.size() >= 2 && lexeme.size() <= 3 && lexeme.at(0) == '\'' &&
           (lexeme.size() == 2 || lexeme.at(1) == 's' || lexeme.at(1) == 'S') &&
           (lexeme.back() == lower || lexeme.back() == upper);
  };
  if (token.kind == TK::IntegerBase) {
    if (rule == binary_number) {
      return matches_base('b', 'B');
    }
    if (rule == octal_number) {
      return matches_base('o', 'O');
    }
    if (rule == hex_number) {
      return matches_base('h', 'H');
    }
    if (rule_name == "@lexer_decimal_number") {
      return matches_base('d', 'D');
    }
  }
  constexpr int kOctalBase = 8;
  constexpr int kHexadecimalBase = 16;
  const auto digit_in_base = [&](int base) {
    return !lexeme.empty() && std::ranges::all_of(lexeme, [&](char ch) {
      if (ch == '_' || ch == 'x' || ch == 'X' || ch == 'z' || ch == 'Z' ||
          ch == '?') {
        return true;
      }
      if (ch >= '0' && ch <= '9') {
        return ch - '0' < base;
      }
      return base == kHexadecimalBase &&
             ((ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F'));
    });
  };
  if (rule_name.starts_with("@lexer_binary_value")) {
    return digit_in_base(2) &&
           (rule_name != "@lexer_binary_value" || lexeme.front() != '_');
  }
  if (rule_name.starts_with("@lexer_octal_value")) {
    return digit_in_base(kOctalBase) &&
           (rule_name != "@lexer_octal_value" || lexeme.front() != '_');
  }
  if (rule_name.starts_with("@lexer_hex_value")) {
    return digit_in_base(kHexadecimalBase) &&
           (rule_name != "@lexer_hex_value" || lexeme.front() != '_');
  }
  if (rule_name == "@lexer_decimal_number") {
    if (token.kind == TK::IntegerLiteral) {
      return !lexeme.empty() && std::ranges::all_of(lexeme, [](char ch) {
        return ch == '_' || (ch >= '0' && ch <= '9');
      });
    }
    if (token.kind == TK::Identifier) {
      const auto& production = kProductions.at(item.production);
      const bool after_question =
          item.dot > 0 && kSymbols.at(production.offset + item.dot - 1) ==
                              -annexTerminal(TK::Question) - 1;
      return !lexeme.empty() &&
             (after_question
                  ? std::ranges::all_of(lexeme,
                                        [](char ch) { return ch == '_'; })
                  : (lexeme.at(0) == 'x' || lexeme.at(0) == 'X' ||
                     lexeme.at(0) == 'z' || lexeme.at(0) == 'Z') &&
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
  if (rule == severity && item.dot == 0) {
    const auto& production = kProductions.at(item.production);
    const int suffix = kSymbols.at(production.offset + 1);
    return suffix == fatal_severity_suffix
               ? lexeme == "$fatal"
               : lexeme == "$error" || lexeme == "$warning" ||
                     lexeme == "$info";
  }
  if (rule == output) {
    return lexeme == "0" || lexeme == "1" || lexeme == "x" || lexeme == "X";
  }
  if (rule == finish_number) {
    return lexeme == "0" || lexeme == "1" || lexeme == "2";
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
    if (kProductions.at(item.production).count == 2) {
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
  if (rule == x_digit) {
    return lexeme == "x" || lexeme == "X";
  }
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
    if (!index.emplace(item, offset).second) {
      return;
    }
    items.push_back(item);
    const int symbol = annexNext(item);
    if (symbol >= 0) {
      waiting[symbol].push_back(offset);
    } else if (symbol == kAnnexCompleteSymbol) {
      const int rule = kProductions.at(item.production).left;
      completed_origins[rule].push_back(item.origin);
      if (item.origin == position) {
        nullable[rule].push_back(offset);
      }
      if (item.origin == 0) {
        completed_roots.insert(rule);
      }
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
        result.at(kProductions.at(i).left).push_back(static_cast<uint16_t>(i));
      }
      return result;
    }();
    charts.emplace_back(0);
    for (const auto name : names) {
      const int rule = annexRule(name);
      if (rule < 0) {
        continue;
      }
      roots.push_back(static_cast<uint16_t>(rule));
      for (const auto production : by_left.at(static_cast<size_t>(rule))) {
        charts.back().add({production, 0, 0});
      }
    }
    close();
  }

  auto close() -> void {
    static const auto by_left = [] {
      std::vector<std::vector<uint16_t>> result(std::size(kRuleNames));
      for (size_t i = 0; i < std::size(kProductions); ++i) {
        result.at(kProductions.at(i).left).push_back(static_cast<uint16_t>(i));
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
      if (total_items + chart.items.size() > kAnnexChartItemLimit) {
        failed = true;
        failure_reason = "Annex A ambiguity resource limit";
        return;
      }
      const AnnexItem item = chart.items.at(cursor);
      const int symbol = annexNext(item);
      if (symbol >= 0) {
        for (const auto child : by_left.at(static_cast<size_t>(symbol))) {
          chart.add({child, 0, position});
        }
        if (const auto found = chart.nullable.find(symbol);
            found != chart.nullable.end() && !found->second.empty()) {
          chart.add({item.production, static_cast<uint16_t>(item.dot + 1),
                     item.origin});
        }
      } else if (symbol == kAnnexCompleteSymbol) {
        const auto& production = kProductions.at(item.production);
        const auto& origin = charts.at(item.origin);
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
              const AnnexItem parent = origin.items.at(index);
              if (parent.dot != 1) {
                continue;
              }
              const int left = kProductions.at(parent.production).left;
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
            const AnnexItem parent = origin.items.at(index);
            if (binary_operator && parent.dot == 1) {
              const int left = kProductions.at(parent.production).left;
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
    if (terminal < 0 || failed || interrupted) {
      return false;
    }
    if (charts.back().scanning.contains(terminal)) {
      return true;
    }
    return std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return !path.failed && !path.interrupted &&
             path.charts.back().scanning.contains(terminal);
    });
  }

  [[nodiscard]] auto checkpoint() const -> Checkpoint {
    Checkpoint saved{charts.size(), total_items, !failed && !interrupted, {}};
    if (!alternatives.empty()) {
      saved.branched_paths.push_back(*this);
    }
    return saved;
  }

  // An opaque item occupies one grammar nonterminal. Resume the enclosing
  // grammar after that item without treating its unknown tokens as terminals.
  [[nodiscard]] auto skipOpaqueItem(Checkpoint saved,
                                    const std::vector<uint16_t>& item_roots)
      -> bool {
    if (!saved.branched_paths.empty()) {
      // Restore every continuation to the point before the unavailable item.
      // A macro may have invalidated some paths while its tokens were read.
      AnnexState restored = std::move(saved.branched_paths.front());
      auto paths = std::move(restored.alternatives);
      restored.alternatives.clear();
      const auto resume = [&](AnnexState& path) {
        return path.skipOpaqueItem({path.charts.size(),
                                    path.total_items,
                                    !path.failed && !path.interrupted,
                                    {}},
                                   item_roots);
      };
      bool valid = resume(restored);
      for (auto& path : paths) {
        valid &= resume(path);
        restored.addContinuation(path);
      }
      *this = std::move(restored);
      if (!valid) {
        interrupted = true;
      }
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
          const AnnexItem parent = origin.items.at(index);
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
    if (failed || interrupted) {
      return true;
    }
    // Earley completions consult the origin chart, so equal FIRST sets at the
    // current position do not imply equal continuations. Keep a single chart
    // only when every item and its origin history agree between branches.
    if (charts.size() != other.charts.size()) {
      return false;
    }
    for (size_t i = 0; i < charts.size(); ++i) {
      if (charts.at(i).items != other.charts.at(i).items) {
        return false;
      }
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
    if (failed || lost_continuation || charts.size() == 1) {
      return false;
    }
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

  [[nodiscard]] auto completedFrom(std::string_view name, size_t origin) const
      -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed) {
      return false;
    }
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
      const auto& production = kProductions.at(item.production);
      if (production.left == rule && item.dot > 0 &&
          kSymbols.at(production.offset + item.dot - 1) == -terminal - 1) {
        return true;
      }
    }
    return std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return path.consumedTerminalInRule(name, kind);
    });
  }

  [[nodiscard]] auto hasViableRule(std::string_view name) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed || charts.empty()) {
      return false;
    }
    return std::ranges::any_of(charts.back().items,
                               [&](AnnexItem item) {
                                 return item.origin == 0 &&
                                        kProductions.at(item.production).left ==
                                            rule;
                               }) ||
           std::ranges::any_of(alternatives, [&](const AnnexState& path) {
             return path.hasViableRule(name);
           });
  }

  [[nodiscard]] auto hasActiveRule(std::string_view name) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed || charts.empty()) {
      return false;
    }
    return std::ranges::any_of(charts.back().items,
                               [&](AnnexItem item) {
                                 return kProductions.at(item.production).left ==
                                        rule;
                               }) ||
           std::ranges::any_of(alternatives, [&](const AnnexState& path) {
             return path.hasActiveRule(name);
           });
  }

  [[nodiscard]] auto allPathsHaveActiveRule(std::string_view name) const
      -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed || interrupted || charts.empty()) {
      return false;
    }
    const bool current =
        std::ranges::any_of(charts.back().items, [&](AnnexItem item) {
          return kProductions.at(item.production).left == rule;
        });
    return current &&
           std::ranges::all_of(alternatives, [&](const AnnexState& path) {
             return path.allPathsHaveActiveRule(name);
           });
  }

  [[nodiscard]] auto hasViableProductionStartingWith(std::string_view name,
                                                     TK kind) const -> bool {
    const int rule = annexRule(name);
    const int terminal = annexTerminal(kind);
    if (rule < 0 || terminal < 0 || failed || charts.empty()) {
      return false;
    }
    return std::ranges::any_of(
               charts.back().items,
               [&](AnnexItem item) {
                 const auto& production = kProductions.at(item.production);
                 return item.origin == 0 && item.dot > 0 &&
                        production.left == rule && production.count > 0 &&
                        kSymbols.at(production.offset) == -terminal - 1;
               }) ||
           std::ranges::any_of(alternatives, [&](const AnnexState& path) {
             return path.hasViableProductionStartingWith(name, kind);
           });
  }

  [[nodiscard]] auto hasActiveProductionContaining(std::string_view name,
                                                   TK kind) const -> bool {
    const int rule = annexRule(name);
    const int terminal = annexTerminal(kind);
    if (rule < 0 || terminal < 0 || failed || charts.empty()) {
      return false;
    }
    return std::ranges::any_of(
               charts.back().items,
               [&](AnnexItem item) {
                 const auto& production = kProductions.at(item.production);
                 if (production.left != rule) {
                   return false;
                 }
                 const auto symbols = std::span(kSymbols).subspan(
                     production.offset, production.count);
                 return std::ranges::find(symbols, -terminal - 1) !=
                        symbols.end();
               }) ||
           std::ranges::any_of(alternatives, [&](const AnnexState& path) {
             return path.hasActiveProductionContaining(name, kind);
           });
  }

  [[nodiscard]] auto expectsRootTerminal(TK kind) const -> bool {
    const int terminal = annexTerminal(kind);
    if (terminal < 0 || failed) {
      return false;
    }
    for (const auto item : charts.back().items) {
      if (item.origin == 0 && annexNext(item) == -terminal - 1 &&
          std::find(roots.begin(), roots.end(),
                    kProductions.at(item.production).left) != roots.end()) {
        return true;
      }
    }
    return std::ranges::any_of(alternatives, [&](const AnnexState& path) {
      return path.expectsRootTerminal(kind);
    });
  }

  auto advance(Token token) -> void {
    if (failed || interrupted) {
      return;
    }
    auto other_paths = std::move(alternatives);
    advanceOne(token);
    for (auto& path : other_paths) {
      path.advanceOne(token);
    }
    lost_continuation |=
        std::ranges::any_of(other_paths, [](const AnnexState& path) {
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
    if (failed) {
      return;
    }
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
        const AnnexItem item = charts.back().items.at(index);
        if (!annexLexemeMatches(item, token)) {
          continue;
        }
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
    bool if_statement_body = false;
    bool conditional_entry_frame = false;
    bool tf_ports_in_header = false;
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
    uint8_t source_modes = 0;
    bool pending_if_begin = false;
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
  static constexpr uint8_t kSourceBeforeDescription = 1;
  static constexpr uint8_t kSourceAfterTimeunits = 2;
  static constexpr uint8_t kSourceAfterDescription = 4;
  static constexpr uint8_t kLibraryText = 8;
  uint8_t source_modes_ = kSourceBeforeDescription | kLibraryText;
  size_t last_grammar_warning_pos_ = std::numeric_limits<size_t>::max();
  bool grammar_suspended_ = false;
  bool stop_at_conditional_boundary_ = false;
  bool pending_if_begin_ = false;
  bool recovery_enabled_ = true;

  // ---- token access ----

  [[nodiscard]] auto peek(size_t offset = 0) const -> Token {
    size_t idx = pos_ + offset;
    return (idx < tokens_.size()) ? tokens_[idx] : tokens_.back();
  }

  [[nodiscard]] auto at(TK kind, size_t offset = 0) const -> bool {
    return peek(offset).kind == kind;
  }

  // Look ahead only to choose between Annex A productions that share an
  // identifier prefix. Their dimension children still validate the tokens
  // when SVParser consumes them. Unavailable macro tokens keep the existing
  // interrupted grammar path.
  [[nodiscard]] auto afterBalancedDimensions(size_t offset) const
      -> std::optional<size_t> {
    while (at(TK::OpenBracket, offset)) {
      int depth = 0;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        if (at(TK::MacroUsage, offset) || at(TK::Directive, offset)) {
          return std::nullopt;
        }
        if (at(TK::Semicolon, offset) || at(TK::EndOfFile, offset) ||
            (!block_stack_.empty() &&
             matchesBlockClose(block_stack_.back().close_kind,
                               peek(offset).kind))) {
          return std::nullopt;
        }
        if (at(TK::OpenBracket, offset)) {
          ++depth;
        }
        if (at(TK::CloseBracket, offset)) {
          --depth;
        }
        ++offset;
      } while (depth > 0 && pos_ + offset < tokens_.size());
      if (depth != 0) {
        return std::nullopt;
      }
    }
    return offset;
  }

  [[nodiscard]] auto afterBalancedParentheses(size_t offset) const
      -> std::optional<size_t> {
    if (!at(TK::OpenParenthesis, offset)) {
      return std::nullopt;
    }
    int depth = 0;
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (at(TK::MacroUsage, offset) || at(TK::Directive, offset)) {
        return std::nullopt;
      }
      if (at(TK::Semicolon, offset) || at(TK::EndOfFile, offset) ||
          (!block_stack_.empty() &&
           matchesBlockClose(block_stack_.back().close_kind,
                             peek(offset).kind))) {
        return std::nullopt;
      }
      if (at(TK::OpenParenthesis, offset)) {
        ++depth;
      }
      if (at(TK::CloseParenthesis, offset)) {
        --depth;
      }
      ++offset;
    } while (depth > 0 && pos_ + offset < tokens_.size());
    if (depth != 0) {
      return std::nullopt;
    }
    return offset;
  }

  [[nodiscard]] auto afterAttributePrefix() const -> std::optional<size_t> {
    size_t offset = 0;
    while (at(TK::OpenParenthesis, offset) && at(TK::Star, offset + 1)) {
      const auto after = afterBalancedParentheses(offset);
      if (!after || !at(TK::Star, *after - 2)) {
        return std::nullopt;
      }
      offset = *after;
    }
    return offset;
  }

  [[nodiscard]] auto afterOrdinaryDirectives(size_t offset) const -> size_t {
    while (isCompilerDirective(peek(offset)) &&
           !isConditionalStartDirective(peek(offset)) &&
           !isConditionalBoundaryDirective(peek(offset))) {
      const std::string_view directive = peek(offset).rawText();
      const bool continued = directive == "`define" || directive == "`pragma" ||
                             directive == "`timescale";
      const size_t source_end =
          std::min(tokens_.back().location().offset(), source_.size());
      size_t end = std::min(peek(offset).location().offset(), source_end);
      while (end < source_end) {
        const size_t newline = source_.find_first_of("\r\n", end);
        if (newline == std::string_view::npos || newline >= source_end) {
          end = source_end;
          break;
        }
        const bool next_line =
            continued && newline > end && source_.at(newline - 1) == '\\';
        end = newline + 1;
        if (source_.at(newline) == '\r' && end < source_end &&
            source_.at(end) == '\n') {
          ++end;
        }
        if (!next_line) {
          break;
        }
      }
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        ++offset;
      } while (pos_ + offset < tokens_.size() &&
               tokens_[pos_ + offset].location().offset() < end);
    }
    return offset;
  }

  // Only distinguish a type name from the following declaration name here.
  // The data_type child validates scopes, parameters and dimensions when it
  // is consumed by the corresponding Annex A production.
  [[nodiscard]] auto afterUserTypePrefix(size_t identifier_offset) const
      -> std::optional<size_t> {
    if (!at(TK::Identifier, identifier_offset)) {
      return std::nullopt;
    }
    size_t next = identifier_offset + 1;
    while (true) {
      if (at(TK::Hash, next) && at(TK::OpenParenthesis, next + 1)) {
        const auto after_parameters = afterBalancedParentheses(next + 1);
        if (!after_parameters) {
          return std::nullopt;
        }
        next = *after_parameters;
      }
      if (!at(TK::DoubleColon, next) || !at(TK::Identifier, next + 1)) {
        break;
      }
      next += 2;
    }
    return afterBalancedDimensions(next);
  }

  [[nodiscard]] auto implicitIdentifierBefore(
      std::initializer_list<TK> boundaries) const -> bool {
    if (!at(TK::Identifier)) {
      return false;
    }
    const auto after_dimensions = afterBalancedDimensions(1);
    return after_dimensions &&
           std::ranges::any_of(boundaries, [&](TK boundary) {
             return at(boundary, afterOrdinaryDirectives(*after_dimensions));
           });
  }

  auto consume() -> Token {
    if (pos_ >= tokens_.size()) {
      return tokens_.back();
    }
    const Token token = tokens_[pos_];
    if (!grammar_suspended_ && token.kind == TK::Directive &&
        !isCompilerDirective(token)) {
      interruptGrammar("macro expansion unavailable to Annex A");
    }
    if (!grammar_suspended_ && token.kind != TK::Directive) {
      for (size_t i = 0; i < grammar_scopes_.size(); ++i) {
        if (grammar_paused_.at(i)) {
          continue;
        }
        auto& scope = grammar_scopes_.at(i);
        if (scope.failed || scope.interrupted) {
          continue;
        }
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
    if (!at(open)) {
      return false;
    }
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
      if (isConditionalStartDirective(peek()) && !grammar_scopes_.empty()) {
        bool header_ended = true;
        const bool resumed = parseAnnexConditional(TK::EndOfFile, header_ended,
                                                   indent_level_, &depth);
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
    if (!grammar_scopes_.empty()) {
      grammar_scopes_.back().interrupted = true;
    }
    return false;
  }

  // The grammar scope identifies the closing delimiter of an expression.
  // Delimiter counting is only used after that scope cannot parse the input.
  auto consumeAnnexDelimited(TK open, TK close, std::string_view rule,
                             Line& line) -> bool {
    if (!at(open)) {
      return false;
    }
    consumeInto(line);
    beginGrammar({rule});
    int depth = 1;
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      const auto& grammar = grammar_scopes_.back();
      if (at(close) && grammar.complete()) {
        static_cast<void>(endGrammar());
        consumeInto(line);
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
      if (at(open)) {
        ++depth;
      }
      if (at(close)) {
        --depth;
      }
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
      if (at(open)) {
        ++depth;
      }
      if (at(close)) {
        --depth;
      }
      consumeInto(line);
    }
    return false;
  }

  [[nodiscard]] auto unavailableMacroIn(size_t begin, size_t end) const
      -> bool {
    for (size_t i = begin; i < end; ++i) {
      if (tokens_[i].kind == TK::MacroUsage ||
          (tokens_[i].kind == TK::Directive &&
           !isCompilerDirective(tokens_[i]))) {
        return true;
      }
    }
    return false;
  }

  [[nodiscard]] auto consumeAnnexRule(
      std::string_view rule, Line& line, std::optional<TK> stop = std::nullopt,
      const std::function<bool()>& should_stop = {}) -> bool {
    beginGrammar({rule});
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      const auto& grammar = grammar_scopes_.back();
      if (grammar.complete() &&
          ((stop && at(*stop)) || (should_stop && should_stop()) ||
           !grammar.accepts(peek().kind))) {
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
    if (!complete) {
      recordGrammarFallback("control outside Annex A rule");
    }
    return complete;
  }

  // Parse a grammar subrule up to its enclosing for-header separator.
  // The second stop protects recovery when a separator is missing.
  auto consumeAnnexUntil(TK stop, TK alternate_stop,
                         const std::vector<std::string_view>& grammar_rules,
                         Line& line) -> bool {
    beginGrammar(grammar_rules);
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
          if (parens > 0) {
            --parens;
          }
          break;
        case TK::OpenBracket:
          ++brackets;
          break;
        case TK::CloseBracket:
          if (brackets > 0) {
            --brackets;
          }
          break;
        case TK::OpenBrace:
        case TK::ApostropheOpenBrace:
          ++braces;
          break;
        case TK::CloseBrace:
          if (braces > 0) {
            --braces;
          }
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
      if (matchingOpenFrame(peek().kind)) {
        break;
      }
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

  // An unexpanded macro inside a struct or union member makes that member's
  // expression unavailable. Keep the rest of the aggregate in the fallback
  // item so its closing brace cannot be mistaken for a sibling declaration.
  auto recoverAggregateAfterMacro(int brace_depth) -> void {
    int conditional_depth = 0;
    while (!at(TK::EndOfFile) && !matchingOpenFrame(peek().kind)) {
      if (isCompilerDirective(peek())) {
        if (stop_at_conditional_boundary_ && conditional_depth == 0 &&
            isConditionalBoundaryDirective(peek())) {
          break;
        }
        if (isConditionalStartDirective(peek())) {
          ++conditional_depth;
        } else if (isConditionalEndDirective(peek()) && conditional_depth > 0) {
          --conditional_depth;
        }
        addLine();
        parseDirectiveLine();
        continue;
      }
      const TK kind = peek().kind;
      if (kind == TK::CloseBrace && brace_depth == 1) {
        addLine();
        if (indent_level_ > 0) {
          --indent_level_;
        }
      }
      consumeInto(line_);
      if (kind == TK::OpenBrace || kind == TK::ApostropheOpenBrace) {
        ++brace_depth;
      } else if (kind == TK::CloseBrace) {
        --brace_depth;
      }
      if (kind == TK::Semicolon) {
        addLine();
        if (brace_depth == 0) {
          return;
        }
      }
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

  struct BlockSpec {
    TK close_kind;
  };

  // Closing tokens are also used to find a safe recovery point. A recovery
  // boundary says nothing about whether Annex A supports the construction.
  [[nodiscard]] static auto blockSpec(TK kind) -> std::optional<BlockSpec> {
    switch (kind) {
      case TK::ModuleKeyword:
      case TK::MacromoduleKeyword:
        return BlockSpec{.close_kind = TK::EndModuleKeyword};
      case TK::InterfaceKeyword:
        return BlockSpec{.close_kind = TK::EndInterfaceKeyword};
      case TK::PackageKeyword:
        return BlockSpec{.close_kind = TK::EndPackageKeyword};
      case TK::ProgramKeyword:
        return BlockSpec{.close_kind = TK::EndProgramKeyword};
      case TK::ClassKeyword:
        return BlockSpec{.close_kind = TK::EndClassKeyword};
      case TK::FunctionKeyword:
        return BlockSpec{.close_kind = TK::EndFunctionKeyword};
      case TK::TaskKeyword:
        return BlockSpec{.close_kind = TK::EndTaskKeyword};
      case TK::GenerateKeyword:
        return BlockSpec{.close_kind = TK::EndGenerateKeyword};
      case TK::BeginKeyword:
        return BlockSpec{.close_kind = TK::EndKeyword};
      case TK::ForkKeyword:
        return BlockSpec{.close_kind = TK::JoinKeyword};
      case TK::CaseKeyword:
      case TK::CaseXKeyword:
      case TK::CaseZKeyword:
        return BlockSpec{.close_kind = TK::EndCaseKeyword};
      case TK::CoverGroupKeyword:
        return BlockSpec{.close_kind = TK::EndGroupKeyword};
      case TK::PropertyKeyword:
        return BlockSpec{.close_kind = TK::EndPropertyKeyword};
      case TK::SequenceKeyword:
        return BlockSpec{.close_kind = TK::EndSequenceKeyword};
      case TK::ClockingKeyword:
        return BlockSpec{.close_kind = TK::EndClockingKeyword};
      case TK::CheckerKeyword:
        return BlockSpec{.close_kind = TK::EndCheckerKeyword};
      case TK::SpecifyKeyword:
        return BlockSpec{.close_kind = TK::EndSpecifyKeyword};
      case TK::PrimitiveKeyword:
        return BlockSpec{.close_kind = TK::EndPrimitiveKeyword};
      case TK::ConfigKeyword:
        return BlockSpec{.close_kind = TK::EndConfigKeyword};
      case TK::TableKeyword:
        return BlockSpec{.close_kind = TK::EndTableKeyword};
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
           (preceding == TK::AssertKeyword || preceding == TK::AssumeKeyword ||
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
  [[nodiscard]] auto findPairedEnd(size_t start, TK close) const
      -> std::optional<size_t> {
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
      if (kind == TK::OpenBrace || kind == TK::ApostropheOpenBrace) {
        nested.push_back(TK::CloseBrace);
        continue;
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
    out.insert(out.end(), tokens_.begin() + static_cast<std::ptrdiff_t>(begin),
               tokens_.begin() + static_cast<std::ptrdiff_t>(end));
  }

  // Include trivia after the previous formatted token. When resuming on a
  // clean source line, leave that line's indentation to the printer.
  auto emitOpaque(size_t begin, size_t resume) -> void {
    // The unsupported-construct diagnostic already identifies this fallback.
    for (auto& scope : grammar_scopes_) {
      scope.interrupted = true;
    }
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

  // Save the emission point for a grammar child. If it fails, restore that
  // point before recovery so each original token is emitted exactly once.
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

  // A semicolon-terminated declaration can resume at its next sibling.
  // Restore the checkpoint before emitting so every source token appears once.
  auto recoverMalformedLeaf(const LeafCheckpoint& saved) -> void {
    lines_.resize(saved.output_size);
    line_ = saved.line;
    preserved_source_end_ = saved.preserved_source_end;
    indent_level_ = saved.indent_level;
    pos_ = saved.pos;
    ListDepth depth;
    while (!at(TK::EndOfFile)) {
      if (depth.topLevel() && at(TK::Semicolon)) {
        consumeInto(line_);
        break;
      }
      if ((depth.topLevel() && matchingOpenFrame(peek().kind)) ||
          (stop_at_conditional_boundary_ &&
           isConditionalBoundaryDirective(peek()))) {
        break;
      }
      if (depth.topLevel() && isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      advanceListDepth(depth, peek().kind);
      consumeInto(line_);
    }
    addLine();
  }

  auto parseGrammarLeaf(bool recover_to_outer = false,
                        const std::optional<LeafCheckpoint>& checkpoint = {},
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
        if (!keep_completed_line_open) {
          addLine();
        }
        return;
      }
      if (at(TK::MacroUsage) ||
          (at(TK::Directive) && !isCompilerDirective(peek()))) {
        if (aggregate_braces > 0) {
          recordGrammarFallback("macro expansion unavailable inside aggregate");
          grammar_scopes_.back().interrupted = true;
          recoverAggregateAfterMacro(aggregate_braces);
          return;
        }
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
      if (!grammar.accepts(peek().kind)) {
        break;
      }
      const TK kind = peek().kind;
      if (kind == TK::StructKeyword || kind == TK::UnionKeyword) {
        aggregate_type = true;
      }
      if (aggregate_type && kind == TK::CloseBrace && aggregate_braces == 1) {
        addLine();
        if (indent_level_ > 0) {
          --indent_level_;
        }
      }
      if (constraint_block && kind == TK::CloseBrace &&
          constraint_braces == 1) {
        addLine();
        if (indent_level_ > 0) {
          --indent_level_;
        }
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
      if (grammar_scopes_.back().failed) {
        break;
      }
    }
    if (!grammar_scopes_.empty() && grammar_scopes_.back().complete()) {
      if (!keep_completed_line_open) {
        addLine();
      }
      return;
    }
    if (!recover_to_outer) {
      recordGrammarFallback(!grammar_scopes_.empty() &&
                                    grammar_scopes_.back().failed
                                ? grammar_scopes_.back().failure_reason
                                : "malformed Annex A item");
      if (!grammar_scopes_.empty()) {
        grammar_scopes_.back().interrupted = true;
      }
      indent_level_ = saved.indent_level;
      consumeUntilSemi();
      return;
    }
    if (!recovery_enabled_) {
      consumeUntilSemi();
      return;
    }
    recordGrammarFallback(!grammar_scopes_.empty() &&
                                  grammar_scopes_.back().failed
                              ? grammar_scopes_.back().failure_reason
                              : "malformed Annex A item");
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
    if (!at(TK::Colon)) {
      return;
    }
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
        .source_modes = source_modes_,
        .pending_if_begin = pending_if_begin_,
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
    source_modes_ = state.source_modes;
    pending_if_begin_ = state.pending_if_begin;
  }

  [[nodiscard]] auto structuralStateCompatible(const ParserState& lhs,
                                               const ParserState& rhs) const
      -> bool {
    if (lhs.indent_level != rhs.indent_level ||
        lhs.block_stack.size() != rhs.block_stack.size() ||
        lhs.grammar_contexts != rhs.grammar_contexts ||
        lhs.grammar_scopes.size() != rhs.grammar_scopes.size() ||
        lhs.grammar_checkpoints.size() != rhs.grammar_checkpoints.size() ||
        lhs.grammar_paused != rhs.grammar_paused ||
        lhs.grammar_summary_owner != rhs.grammar_summary_owner ||
        lhs.pending_if_begin != rhs.pending_if_begin) {
      return false;
    }
    for (size_t i = 0; i < lhs.block_stack.size(); ++i) {
      const auto& left = lhs.block_stack.at(i);
      const auto& right = rhs.block_stack.at(i);
      if (left.close_kind != right.close_kind ||
          left.extra_dedent_after_close != right.extra_dedent_after_close ||
          left.grammar_body != right.grammar_body ||
          left.constructor_body != right.constructor_body ||
          left.if_statement_body != right.if_statement_body ||
          left.tf_ports_in_header != right.tf_ports_in_header ||
          ((left.close_kind == TK::EndConfigKeyword ||
            left.close_kind == TK::EndPrimitiveKeyword) &&
           left.statement_phase != right.statement_phase)) {
        return false;
      }
    }
    for (size_t i = 0; i < lhs.grammar_scopes.size(); ++i) {
      const auto& left = lhs.grammar_scopes.at(i);
      const auto& right = rhs.grammar_scopes.at(i);
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
        joined.block_stack.at(i).statement_phase |=
            state.block_stack.at(i).statement_phase;
        joined.block_stack.at(i).udp_has_entry &=
            state.block_stack.at(i).udp_has_entry;
        joined.block_stack.at(i).udp_sequential |=
            state.block_stack.at(i).udp_sequential;
        joined.block_stack.at(i).udp_combinational |=
            state.block_stack.at(i).udp_combinational;
        joined.block_stack.at(i).udp_port_on_all_paths &=
            state.block_stack.at(i).udp_port_on_all_paths;
        joined.block_stack.at(i).udp_port_on_any_path |=
            state.block_stack.at(i).udp_port_on_any_path;
        joined.block_stack.at(i).udp_initial_seen |=
            state.block_stack.at(i).udp_initial_seen;
      }
      for (size_t i = 0; i < joined.grammar_scopes.size(); ++i) {
        joined.grammar_scopes.at(i).addContinuation(state.grammar_scopes.at(i));
      }
      joined.source_modes |= state.source_modes;
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
    for (auto& frame : block_stack_) {
      frame.conditional_entry_frame = true;
    }
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

  [[nodiscard]] auto atEnclosingBoundary() const -> bool {
    if (at(TK::EndOfFile) || (stop_at_conditional_boundary_ &&
                              isConditionalBoundaryDirective(peek()))) {
      return true;
    }
    return std::ranges::any_of(block_stack_, [&](const BlockFrame& frame) {
      return matchesBlockClose(frame.close_kind, peek().kind);
    });
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
      // anonymous_program and randsequence_statement end without a label.
      // class_constructor_declaration permits only ': new'. Other labeled
      // closers use the identifier terminal in their Annex A production.
      const bool label_allowed =
          closeAllowsLabel(frame.close_kind) &&
          !(frame.close_kind == TK::EndProgramKeyword &&
            frame.grammar_body == "anonymous_program_item") &&
          !(frame.close_kind == TK::EndSequenceKeyword &&
            frame.grammar_body == "rs_production");
      const bool label_terminal = frame.constructor_body
                                      ? at(TK::NewKeyword, 1)
                                      : at(TK::Identifier, 1);
      if (label_allowed && label_terminal) {
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
    // A conditional compilation branch can close the begin body of an if
    // before the recursive parseIf() call regains control. Continue that
    // Annex A conditional_statement inside the branch.
    if (stop_at_conditional_boundary_ && frame.conditional_entry_frame &&
        frame.if_statement_body && at(TK::ElseKeyword)) {
      if (indent_level_ > 0) {
        --indent_level_;
      }
      consumeInto(line_);
      if (at(TK::IfKeyword)) {
        parseIf(false);
      } else {
        addLine();
        parseIndentedStatement({"statement_or_null"});
      }
    }
  }

  auto pushOpenFrame(TK closeKind) -> void {
    block_stack_.push_back(BlockFrame{.close_kind = closeKind,
                                      .extra_dedent_after_close = 0,
                                      .grammar_body = {}});
  }

  auto parseDelimitedBody(TK closeKind, std::string_view bodyRule = {},
                          bool constructorBody = false,
                          bool tfPortsInHeader = false,
                          bool ifStatementBody = false) -> void {
    pushOpenFrame(closeKind);
    block_stack_.back().grammar_body = bodyRule;
    block_stack_.back().constructor_body = constructorBody;
    block_stack_.back().tf_ports_in_header = tfPortsInHeader;
    block_stack_.back().if_statement_body = ifStatementBody;
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
        if (waiting.contains(annexRule(root))) {
          expected.push_back(root);
        }
      }
      if (!expected.empty()) {
        roots = std::move(expected);
      }
    }
    ++indent_level_;
    grammar_contexts_.push_back({block_stack_.size(), std::move(roots)});
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek()) &&
           !isConditionalBoundaryDirective(peek())) {
      parseStatement();
    }
    parseStatement();
    grammar_contexts_.pop_back();
    if (block_stack_.size() == stack_size_before) {
      --indent_level_;
    } else if (!block_stack_.empty()) {
      ++block_stack_.back().extra_dedent_after_close;
    }
  }

  auto recordGrammarFallback(std::string_view reason) -> void {
    if (last_grammar_warning_pos_ == pos_) {
      return;
    }
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
      if (it->block_depth == block_stack_.size()) {
        return it->roots;
      }
    }
    if (block_stack_.empty()) {
      std::vector<std::string_view> roots;
      if (static_cast<unsigned>(source_modes_) &
          (static_cast<unsigned>(kSourceBeforeDescription) |
           static_cast<unsigned>(kSourceAfterTimeunits) |
           static_cast<unsigned>(kSourceAfterDescription))) {
        roots.emplace_back("description");
      }
      if (source_modes_ & kSourceBeforeDescription) {
        roots.emplace_back("timeunits_declaration");
      }
      if (source_modes_ & kLibraryText) {
        roots.emplace_back("library_description");
      }
      return roots;
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
        if (udp.statement_phase) {
          return {};
        }
        std::vector<std::string_view> roots;
        if (!udp.udp_initial_seen) {
          if (!udp.udp_ansi_header) {
            roots.emplace_back("udp_port_declaration");
          }
          roots.emplace_back("udp_initial_statement");
          roots.emplace_back("combinational_body");
        }
        roots.emplace_back("sequential_body");
        return roots;
      }
      if (block_stack_.back().grammar_body == "udp_table_entry") {
        std::vector<std::string_view> roots;
        if (!block_stack_.back().udp_sequential) {
          roots.emplace_back("combinational_entry");
        }
        if (!block_stack_.back().udp_combinational) {
          roots.emplace_back("sequential_entry");
        }
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
                     ? std::vector<
                           std::string_view>{"function_statement_or_null"}
                     : std::vector<std::string_view>{
                           "block_item_declaration",
                           "function_statement_or_null"};
        }
        return block_stack_.back().statement_phase
                   ? std::vector<std::string_view>{"function_statement_or_null"}
               : block_stack_.back().tf_ports_in_header
                   ? std::vector<std::string_view>{"block_item_declaration",
                                                   "function_statement_or_null"}
                   : std::vector<std::string_view>{
                         "tf_item_declaration", "function_statement_or_null"};
      case TK::EndTaskKeyword:
        return block_stack_.back().statement_phase
                   ? std::vector<std::string_view>{"statement_or_null"}
               : block_stack_.back().tf_ports_in_header
                   ? std::vector<std::string_view>{"block_item_declaration",
                                                   "statement_or_null"}
                   : std::vector<std::string_view>{"tf_item_declaration",
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

  auto beginGrammar(const std::vector<std::string_view>& roots,
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
    if (grammar_scopes_.size() < 2 || !grammar_checkpoints_.back()) {
      return;
    }
    const size_t parent_index = grammar_scopes_.size() - 2;
    const auto& parent = grammar_scopes_.at(parent_index);
    if (grammar_paused_.at(parent_index) || parent.failed ||
        parent.interrupted) {
      return;
    }
    const auto& waiting = parent.charts.back().waiting;
    const auto& roots = grammar_scopes_.back().roots;
    bool has_candidate = false;
    bool all_candidates_waited = true;
    for (const uint16_t root : roots) {
      if (!annexCanStart(kRuleNames.at(root), peek().kind)) {
        continue;
      }
      has_candidate = true;
      all_candidates_waited &= waiting.contains(root);
    }
    if (has_candidate && all_candidates_waited) {
      grammar_paused_.at(parent_index) = true;
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
      if (summarized) {
        grammar_paused_.back() = false;
      }
      if (summarized || state.failed || state.interrupted) {
        std::vector<uint16_t> completed_roots;
        if (summarized && state.complete()) {
          for (const uint16_t root : state.roots) {
            if (state.completed(kRuleNames.at(root)) &&
                grammar_scopes_.back()
                    .charts.at(checkpoint->chart_count - 1)
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
    if (interrupted) {
      recordGrammarFallback(reason);
    }
  }

  // ---- grammar ----

  // NOLINTBEGIN(misc-no-recursion)

  // source_text ::= [ timeunits_declaration ] { description };
  // library_text ::= { library_description }. Keep only the continuations
  // allowed by the next Annex A top-level production, including both paths
  // while a config declaration or ';' remains ambiguous.
  [[nodiscard]] auto nextSourceModes(TK first) const -> uint8_t {
    uint8_t next = 0;
    if ((source_modes_ & kSourceBeforeDescription) &&
        annexCanStart("timeunits_declaration", first)) {
      next |= kSourceAfterTimeunits;
    }
    if ((static_cast<unsigned>(source_modes_) &
         (static_cast<unsigned>(kSourceBeforeDescription) |
          static_cast<unsigned>(kSourceAfterTimeunits) |
          static_cast<unsigned>(kSourceAfterDescription))) &&
        annexCanStart("description", first)) {
      next |= kSourceAfterDescription;
    }
    if ((source_modes_ & kLibraryText) &&
        annexCanStart("library_description", first)) {
      next |= kLibraryText;
    }
    return next;
  }

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

  [[nodiscard]] auto parseAttributeMacroInterruptionRule() -> bool {
    if (!at(TK::MacroUsage) &&
        !(at(TK::Directive) && !isCompilerDirective(peek()))) {
      return false;
    }
    parseMacroStatement();
    return true;
  }

  // description ::= module_declaration | udp_declaration |
  // interface_declaration | program_declaration | package_declaration |
  // ... | config_declaration. The keyword alternatives enter their rule
  // functions directly; shared-prefix alternatives still use local grammar
  // state in parseStatement().
  auto parseDescriptionRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      // description admits attributes on structural headers, package_item
      // and bind_directive, but not on config or extern alternatives.
      if (valid &&
          annexCanStartAny(
              {"module_nonansi_header", "udp_declaration",
               "interface_nonansi_header", "program_nonansi_header",
               "package_declaration", "package_item", "bind_directive"},
              peek().kind) &&
          parseDescriptionRule()) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed description");
      recoverMalformedItem(saved);
      return true;
    }
    switch (peek().kind) {
      case TK::ExternKeyword:
        if (at(TK::PrimitiveKeyword, 1)) {
          parsePrimitiveBlock();
        } else if (!parseExternStructuralDeclarationRule()) {
          static_cast<void>(parseAnnexItem({"description"}, true));
        }
        return true;
      case TK::ModuleKeyword:
      case TK::MacromoduleKeyword:
        parseStructuralBlock(TK::EndModuleKeyword);
        return true;
      case TK::InterfaceKeyword:
        if (at(TK::ClassKeyword, 1)) {
          return parsePackageOrGenerateDeclarationRule();
        }
        parseStructuralBlock(TK::EndInterfaceKeyword);
        return true;
      case TK::ProgramKeyword:
        if (at(TK::Semicolon, 1)) {
          return parseAnonymousProgramRule();
        }
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
      case TK::ConstraintKeyword:
        return parsePackageOrGenerateDeclarationRule();
      case TK::StaticKeyword:
      case TK::VirtualKeyword:
        return parsePackageItemRule();
      case TK::BindKeyword:
        return parseModuleCommonLeafRule();
      default:
        return parsePackageItemRule();
    }
  }

  auto parseLibraryDescriptionRule() -> bool {
    if (at(TK::ConfigKeyword)) {
      parseConfigBlock();
      return true;
    }
    if (at(TK::LibraryKeyword) || at(TK::IncludeKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      recordGrammarFallback(
          "Annex A file_path_spec has no production in the available grammar");
      recoverMalformedLeaf(saved);
      return true;
    }
    return false;
  }

  // The extern alternatives of module_declaration, interface_declaration,
  // and program_declaration contain only one ANSI or non-ANSI header.
  auto parseExternStructuralDeclarationRule() -> bool {
    std::vector<std::string_view> headers;
    TK close_kw = TK::EndOfFile;
    if (at(TK::ModuleKeyword, 1) || at(TK::MacromoduleKeyword, 1)) {
      headers = {"module_nonansi_header", "module_ansi_header"};
      close_kw = TK::EndModuleKeyword;
    } else if (at(TK::InterfaceKeyword, 1)) {
      headers = {"interface_nonansi_header", "interface_ansi_header"};
      close_kw = TK::EndInterfaceKeyword;
    } else if (at(TK::ProgramKeyword, 1)) {
      headers = {"program_nonansi_header", "program_ansi_header"};
      close_kw = TK::EndProgramKeyword;
    } else {
      return false;
    }
    if (parseStructuralHeaderRule(close_kw, true)) {
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // extern
    beginGrammar(headers);
    parseGrammarLeaf(false, {}, true);
    const AnnexState header = endGrammar();
    if (header.failed || header.interrupted || !header.complete()) {
      recordGrammarFallback("invalid Annex A extern declaration header");
      recoverMalformedLeaf(saved);
    }
    return true;
  }

  // module_item ::= port_declaration ';' | non_port_module_item. Enter the
  // distinct non_port_module_item productions here; shared-prefix ports,
  // declarations and instantiations retain their local item chart.
  auto parseModuleItemRule(bool allow_port_declaration) -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      // non_port_module_item admits this prefix only for these children.
      if (valid &&
          annexCanStartAny({"module_or_generate_item", "specparam_declaration"},
                           peek().kind) &&
          parseModuleItemRule(false)) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed module item");
      recoverMalformedItem(saved);
      return true;
    }
    if (parseTimeunitsRule()) {
      return true;
    }
    if (parseDefaultClockingOrDisableRule(false)) {
      return true;
    }
    if (allow_port_declaration &&
        (at(TK::InputKeyword) || at(TK::OutputKeyword) ||
         at(TK::InOutKeyword) || at(TK::RefKeyword))) {
      parsePortDeclarationRule();
      return true;
    }
    if (allow_port_declaration &&
        parseQualifiedInterfacePortDeclarationRule()) {
      return true;
    }
    if (parseParameterDeclarationRule()) {
      return true;
    }
    if (at(TK::UnitSystemName) &&
        annexCanStart("checker_instantiation", peek().kind) &&
        parseStructuralInstantiationRule()) {
      return true;
    }
    switch (peek().kind) {
      case TK::GenerateKeyword:
        parseSimpleBlock(TK::EndGenerateKeyword);
        return true;
      case TK::ModuleKeyword:
      case TK::MacromoduleKeyword:
        parseStructuralBlock(TK::EndModuleKeyword);
        return true;
      case TK::InterfaceKeyword:
        if (at(TK::ClassKeyword, 1)) {
          return parsePackageOrGenerateDeclarationRule();
        }
        parseStructuralBlock(TK::EndInterfaceKeyword);
        return true;
      case TK::ProgramKeyword:
        parseStructuralBlock(TK::EndProgramKeyword);
        return true;
      case TK::SpecifyKeyword:
        parseSpecifyBlockRule();
        return true;
      case TK::SpecParamKeyword:
        parseSpecparamDeclarationRule();
        return true;
      default:
        break;
    }
    if (parseTypeDeclarationRule() || parseExplicitDataDeclarationRule() ||
        parseNettypeDeclarationRule() || parseNetDeclarationRule() ||
        parseParameterOverrideRule() || parseAssertionItemRule() ||
        parseModuleCommonLeafRule() ||
        parsePackageOrGenerateDeclarationRule() ||
        parseGenerateConstructRule()) {
      return true;
    }
    if (parseGateInstantiationRule() || parseUdpInstantiationRule() ||
        parseStructuralInstantiationRule() || parseUserDataDeclarationRule()) {
      return true;
    }
    if (parseClockingDeclarationRule()) {
      return true;
    }
    return parseProceduralConstructRule(true);
  }

  auto parseParameterOverrideRule() -> bool {
    if (!at(TK::DefParamKeyword)) {
      return false;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    bool conditional = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      if (isConditionalStartDirective(tokens_[i])) {
        conditional = true;
        break;
      }
      if (tokens_[i].kind == TK::Semicolon ||
          tokens_[i].kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    const bool valid =
        conditional_members
            ? parseConditionalAnnexCommaListRule("list_of_defparam_assignments",
                                                 "defparam_assignment")
        : conditional ? consumeAnnexRule("list_of_defparam_assignments", line_,
                                         TK::Semicolon)
                      : parseConstantParameterAssignmentListRule(
                            "hierarchical_parameter_identifier");
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A parameter override");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // defparam_assignment and the ordinary specparam_assignment alternative
  // share '= constant_mintypmax_expression' after their identifier child.
  [[nodiscard]] auto parseConstantParameterAssignmentRule(
      std::string_view identifier) -> bool {
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule(identifier, line_, TK::Comma,
                          [&] { return at(TK::Equals); })) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::Equals)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    return consumeAnnexRule("constant_mintypmax_expression", line_, TK::Comma,
                            [&] { return at(TK::Semicolon); });
  }

  [[nodiscard]] auto parseConstantParameterAssignmentListRule(
      std::string_view identifier, bool pulse_control = false) -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      parseGrammarChildDirectiveLines();
      const bool pulse = pulse_control && at(TK::Identifier) &&
                         peek().rawText().starts_with("PATHPULSE$");
      const bool valid =
          pulse ? consumeAnnexRule("pulse_control_specparam", line_, TK::Comma)
                : parseConstantParameterAssignmentRule(identifier);
      if (!valid) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // A conditional after a list separator can contribute complete members to
  // either branch. Other interrupted positions stay with the parent rule's
  // diagnostic path because they may split an individual grammar child.
  [[nodiscard]] auto hasConditionalListMember(
      size_t start, TK terminator = TK::Semicolon) const -> bool {
    ListDepth depth;
    int conditionals = 0;
    bool found = false;
    std::optional<TK> branch_last;
    for (size_t i = start; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token)) {
        if (conditionals != 0 || i == start ||
            tokens_[i - 1].kind != TK::Comma || !depth.topLevel()) {
          return false;
        }
        ++conditionals;
        found = true;
        branch_last.reset();
        continue;
      }
      if (isConditionalAlternativeDirective(token) && conditionals > 0) {
        if (branch_last != TK::Comma) {
          return false;
        }
        branch_last.reset();
        continue;
      }
      if (isConditionalEndDirective(token)) {
        if (conditionals == 0 || branch_last != TK::Comma) {
          return false;
        }
        --conditionals;
        branch_last = TK::Comma;
        continue;
      }
      if (token.kind == terminator && depth.topLevel()) {
        if (conditionals > 0) {
          return false;
        }
        break;
      }
      if (token.kind == TK::EndOfFile) {
        break;
      }
      if (conditionals > 0 && depth.topLevel()) {
        branch_last = token.kind;
      }
      advanceListDepth(depth, token.kind);
    }
    return found && conditionals == 0;
  }

  [[nodiscard]] auto hasAnnexListInterruption(
      size_t start, bool conditional_members,
      TK terminator = TK::Semicolon) const -> bool {
    ListDepth depth;
    for (size_t i = start; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if ((isConditionalStartDirective(token) && !conditional_members) ||
          token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        return true;
      }
      if ((token.kind == terminator && depth.topLevel()) ||
          token.kind == TK::EndOfFile) {
        break;
      }
      advanceListDepth(depth, token.kind);
    }
    return false;
  }

  [[nodiscard]] auto hasAnnexHeaderInterruption(size_t start,
                                                bool conditional_ports) const
      -> bool {
    ListDepth depth;
    for (size_t i = start; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if ((isConditionalStartDirective(token) &&
           !(conditional_ports && depth.parens == 1 && depth.brackets == 0 &&
             depth.braces == 0)) ||
          token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        return true;
      }
      if ((token.kind == TK::Semicolon && depth.topLevel()) ||
          token.kind == TK::EndOfFile) {
        break;
      }
      advanceListDepth(depth, token.kind);
    }
    return false;
  }

  // Keep the list production live when a branch supplies comma-separated
  // children. Ordinary members still enter their own Annex A child rule;
  // parseAnnexConditional advances the same list state through each branch.
  auto parseConditionalAnnexCommaListRule(
      std::string_view list,  // NOLINT(bugprone-easily-swappable-parameters)
      std::string_view child, TK terminator = TK::Semicolon) -> bool {
    beginGrammar({list});
    bool valid = true;
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      if (grammar_scopes_.back().complete() && at(terminator)) {
        break;
      }
      if (isConditionalStartDirective(peek())) {
        bool ended = true;
        valid = parseAnnexConditional(TK::EndOfFile, ended, indent_level_);
      } else if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      } else if (at(TK::Comma)) {
        valid = grammar_scopes_.back().accepts(TK::Comma);
        if (valid) {
          consumeInto(line_);
        }
      } else {
        valid = grammar_scopes_.back().accepts(peek().kind) &&
                consumeAnnexRule(child, line_, TK::Comma);
      }
      if (!valid || grammar_scopes_.back().failed ||
          grammar_scopes_.back().interrupted) {
        break;
      }
    }
    const AnnexState result = endGrammar(false);
    return valid && !result.failed && !result.interrupted &&
           result.complete() && at(terminator);
  }

  // specparam_declaration ::= specparam [packed_dimension]
  //                             list_of_specparam_assignments ';'.
  auto parseSpecparamAssignmentListRule() -> bool {
    return parseConstantParameterAssignmentListRule("specparam_identifier",
                                                    true);
  }

  auto parseSpecparamDeclarationRule() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    const bool conditional_members = hasConditionalListMember(pos_);
    bool conditional = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      if (isConditionalStartDirective(tokens_[i])) {
        conditional = true;
        break;
      }
      if (tokens_[i].kind == TK::Semicolon ||
          tokens_[i].kind == TK::EndOfFile) {
        break;
      }
    }
    consumeInto(line_);
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (at(TK::OpenBracket) && !consumeAnnexRule("packed_dimension", line_)) {
      recordGrammarFallback("invalid Annex A specparam dimension");
      recoverMalformedItem(saved);
      return;
    }
    skip_directives();
    const bool valid =
        conditional_members
            ? parseConditionalAnnexCommaListRule(
                  "list_of_specparam_assignments", "specparam_assignment")
        : conditional ? consumeAnnexRule("list_of_specparam_assignments", line_,
                                         TK::Semicolon)
                      : parseSpecparamAssignmentListRule();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A specparam assignment list");
      recoverMalformedItem(saved);
      return;
    }
    consumeInto(line_);
    addLine();
  }

  // specify_{input,output}_terminal_descriptor ::= identifier
  // [ '[' constant_range_expression ']' ].
  [[nodiscard]] auto parseSpecifyTerminalDescriptorRule(bool output) -> bool {
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule(output ? "output_identifier" : "input_identifier",
                          line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (at(TK::OpenBracket) &&
        !consumeAnnexDelimited(TK::OpenBracket, TK::CloseBracket,
                               "constant_range_expression", line_)) {
      return false;
    }
    return true;
  }

  auto parseSpecifyOutputListRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseSpecifyTerminalDescriptorRule(true)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // A.7.2: the path operator selects the parallel or full production. Parse
  // its terminal descriptors as children while emitting the same flat line.
  [[nodiscard]] auto parseSpecifyPathDescriptionRule(bool allow_edge) -> bool {
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    const bool edge =
        allow_edge && annexCanStart("edge_identifier", peek().kind);
    if (edge && !consumeAnnexRule("edge_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!parseSpecifyTerminalDescriptorRule(false)) {
      return false;
    }
    size_t inputs = 1;
    parseGrammarChildDirectiveLines();
    while (at(TK::Comma)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!parseSpecifyTerminalDescriptorRule(false)) {
        return false;
      }
      ++inputs;
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::Plus) || at(TK::Minus)) {
      if (!consumeAnnexRule("polarity_operator", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    const bool parallel = at(TK::EqualsArrow);
    if (!parallel && !at(TK::StarArrow)) {
      return false;
    }
    if (parallel && inputs != 1) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    const bool data_source = at(TK::OpenParenthesis);
    if (data_source) {
      if (!allow_edge) {
        return false;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
    }
    if (!parseSpecifyTerminalDescriptorRule(true)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!parallel) {
      while (at(TK::Comma)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
        if (!parseSpecifyTerminalDescriptorRule(true)) {
          return false;
        }
        parseGrammarChildDirectiveLines();
      }
    }
    if (data_source) {
      // slang lexes the adjacent Annex A polarity and ':' terminals as one
      // token in the common +: / -: spelling.
      const bool combined_polarity = at(TK::PlusColon) || at(TK::MinusColon);
      if (combined_polarity) {
        consumeInto(line_);
      } else if (at(TK::Plus) || at(TK::Minus)) {
        if (!consumeAnnexRule("polarity_operator", line_)) {
          return false;
        }
        parseGrammarChildDirectiveLines();
      }
      if (!combined_polarity) {
        if (!at(TK::Colon)) {
          return false;
        }
        consumeInto(line_);
      }
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("data_source_expression", line_,
                            TK::CloseParenthesis)) {
        return false;
      }
      if (!at(TK::CloseParenthesis)) {
        return false;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
    }
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // A.7.5.3: reference_event and data_event are timing_check_event;
  // controlled_reference_event requires its event control. The descriptor
  // child keeps the input/output terminal ambiguity local.
  [[nodiscard]] auto parseTimingCheckEventRule(bool controlled) -> bool {
    parseGrammarChildDirectiveLines();
    const bool has_control =
        at(TK::PosEdgeKeyword) || at(TK::NegEdgeKeyword) || at(TK::EdgeKeyword);
    if (controlled && !has_control) {
      return false;
    }
    if (has_control && !consumeAnnexRule("timing_check_event_control", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("specify_terminal_descriptor", line_, TK::Comma, [&] {
          return at(TK::TripleAnd) || at(TK::CloseParenthesis);
        })) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (at(TK::TripleAnd)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("timing_check_condition", line_, TK::Comma,
                            [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    return true;
  }

  // A.7.5.1 selects a timing-check production by its system identifier. The
  // argument slots below follow that production; each nonempty slot invokes
  // its A.7.5.2 child while tokens are emitted.
  [[nodiscard]] auto parseSpecifyTimingCheckRule() -> bool {
    if (!at(TK::SystemIdentifier)) {
      return false;
    }
    const std::string_view name = peek().rawText();
    std::vector<std::string_view> required;
    std::vector<std::string_view> optional;
    if (name == "$setup") {
      required = {"data_event", "reference_event", "timing_check_limit"};
    } else if (name == "$period") {
      required = {"controlled_reference_event", "timing_check_limit"};
    } else if (name == "$width") {
      required = {"controlled_reference_event", "timing_check_limit",
                  "threshold"};
    } else if (name == "$nochange") {
      required = {"reference_event", "data_event", "start_edge_offset",
                  "end_edge_offset"};
    } else if (name == "$hold" || name == "$recovery" || name == "$removal" ||
               name == "$skew" || name == "$timeskew" || name == "$fullskew" ||
               name == "$setuphold" || name == "$recrem") {
      required = {"reference_event", "data_event", "timing_check_limit"};
      if (name == "$fullskew" || name == "$setuphold" || name == "$recrem") {
        required.emplace_back("timing_check_limit");
      }
    } else {
      return false;
    }
    optional.emplace_back("notifier");
    if (name == "$timeskew" || name == "$fullskew") {
      optional.emplace_back("event_based_flag");
      optional.emplace_back("remain_active_flag");
    } else if (name == "$setuphold" || name == "$recrem") {
      optional.insert(optional.end(),
                      {"timestamp_condition", "timecheck_condition",
                       "delayed_reference", "delayed_data"});
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    for (size_t i = 0; i < required.size(); ++i) {
      parseGrammarChildDirectiveLines();
      if (i > 0) {
        if (!at(TK::Comma)) {
          return false;
        }
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
      }
      const std::string_view child = required.at(i);
      const bool event = child == "data_event" || child == "reference_event" ||
                         child == "controlled_reference_event";
      if (!(event ? parseTimingCheckEventRule(child ==
                                              "controlled_reference_event")
                  : consumeAnnexRule(child, line_, TK::Comma, [&] {
                      return at(TK::CloseParenthesis);
                    }))) {
        return false;
      }
    }
    for (const auto child : optional) {
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma) && !at(TK::CloseParenthesis) &&
          !consumeAnnexRule(child, line_, TK::Comma,
                            [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!at(TK::Semicolon)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // path_delay_value ::= list_of_path_delay_expressions |
  //                      '(' list_of_path_delay_expressions ')'.
  [[nodiscard]] auto parseSpecifyPathDelayRule() -> bool {
    parseGrammarChildDirectiveLines();
    const bool parenthesized = at(TK::OpenParenthesis);
    if (parenthesized) {
      consumeInto(line_);
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule(
            "list_of_path_delay_expressions", line_,
            parenthesized ? TK::CloseParenthesis : TK::Semicolon)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (parenthesized) {
      if (!at(TK::CloseParenthesis)) {
        return false;
      }
      consumeInto(line_);
    }
    return true;
  }

  auto parseSpecifyItemRule() -> bool {
    if (at(TK::SpecParamKeyword)) {
      parseSpecparamDeclarationRule();
      return true;
    }
    const bool pulse =
        at(TK::PulseStyleOnEventKeyword) || at(TK::PulseStyleOnDetectKeyword);
    const bool cancel =
        at(TK::ShowCancelledKeyword) || at(TK::NoShowCancelledKeyword);
    if (pulse || cancel) {
      const LeafCheckpoint saved = leafCheckpoint();
      const bool conditional_members = hasConditionalListMember(pos_);
      const bool interrupted =
          hasAnnexListInterruption(pos_, conditional_members);
      consumeInto(line_);
      if (!(interrupted
                ? consumeAnnexRule("list_of_path_outputs", line_, TK::Semicolon)
            : conditional_members ? parseConditionalAnnexCommaListRule(
                                        "list_of_path_outputs",
                                        "specify_output_terminal_descriptor")
                                  : parseSpecifyOutputListRule()) ||
          !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A specify output list");
        recoverMalformedLeaf(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    const bool path =
        at(TK::OpenParenthesis) || at(TK::IfKeyword) || at(TK::IfNoneKeyword);
    const bool timing = at(TK::SystemIdentifier);
    if (!path && !timing) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = false;
    if (path) {
      const bool ifnone = at(TK::IfNoneKeyword);
      const bool interrupted = hasAnnexListInterruption(pos_, false);
      if (at(TK::IfKeyword)) {
        consumeInto(line_);
        valid = consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                      "module_path_expression", line_);
      } else {
        if (ifnone) {
          consumeInto(line_);
        }
        valid = true;
      }
      if (valid) {
        if (interrupted) {
          std::vector<std::string_view> descriptions{
              "parallel_path_description", "full_path_description"};
          if (!ifnone) {
            descriptions.emplace_back(
                "parallel_edge_sensitive_path_description");
            descriptions.emplace_back("full_edge_sensitive_path_description");
          }
          const AnnexState description =
              parseAnnexItem(descriptions, false, true);
          valid = !description.failed && !description.interrupted &&
                  description.complete();
        } else {
          valid = parseSpecifyPathDescriptionRule(!ifnone);
        }
      }
      if (valid && at(TK::Equals)) {
        consumeInto(line_);
        valid = parseSpecifyPathDelayRule();
      } else {
        valid = false;
      }
      if (valid && at(TK::Semicolon)) {
        consumeInto(line_);
      } else {
        valid = false;
      }
    } else {
      valid = hasAnnexListInterruption(pos_, false)
                  ? consumeAnnexRule("system_timing_check", line_)
                  : parseSpecifyTimingCheckRule();
    }
    if (!valid || line_.tokens.empty() ||
        line_.tokens.back().kind != TK::Semicolon) {
      recordGrammarFallback("invalid Annex A specify item");
      recoverMalformedLeaf(saved);
      return true;
    }
    addLine();
    return true;
  }

  auto parseTimeunitsRule() -> bool {
    if (!at(TK::TimeUnitKeyword) && !at(TK::TimePrecisionKeyword)) {
      return false;
    }
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      if (tokens_[i].kind == TK::Semicolon ||
          tokens_[i].kind == TK::EndOfFile) {
        break;
      }
      if (isConditionalStartDirective(tokens_[i])) {
        static_cast<void>(parseAnnexItem({"timeunits_declaration"}));
        return true;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const TK first = peek().kind;
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    const auto parse_clause = [&](TK keyword, bool& slash) -> bool {
      if (!at(keyword)) {
        return false;
      }
      consumeInto(line_);
      skip_directives();
      // slang has already combined Annex A time_literal into TimeLiteral.
      if (!at(TK::TimeLiteral)) {
        return false;
      }
      consumeInto(line_);
      skip_directives();
      if (keyword == TK::TimeUnitKeyword && at(TK::Slash)) {
        slash = true;
        consumeInto(line_);
        skip_directives();
        if (!at(TK::TimeLiteral)) {
          return false;
        }
        consumeInto(line_);
        skip_directives();
      }
      if (!at(TK::Semicolon)) {
        return false;
      }
      consumeInto(line_);
      addLine();
      return true;
    };
    bool first_slash = false;
    bool valid = parse_clause(first, first_slash);
    if (valid) {
      skip_directives();
      const TK second = first == TK::TimeUnitKeyword ? TK::TimePrecisionKeyword
                                                     : TK::TimeUnitKeyword;
      if (!first_slash && at(second)) {
        bool second_slash = false;
        valid = parse_clause(second, second_slash) && !second_slash;
      }
    }
    if (!valid) {
      recordGrammarFallback("invalid Annex A timeunits declaration");
      recoverMalformedItem(saved);
    }
    return true;
  }

  auto parseTypeDeclarationRule() -> bool {
    if (!at(TK::TypedefKeyword)) {
      return false;
    }
    if (hasAnnexListInterruption(pos_, false)) {
      static_cast<void>(parseAnnexItem({"type_declaration"}, true));
      return true;
    }
    const size_t type_start = afterOrdinaryDirectives(1);
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    if (at(TK::Identifier, type_start)) {
      const auto after_selects = afterBalancedDimensions(type_start + 1);
      if (after_selects && at(TK::Dot, *after_selects)) {
        const LeafCheckpoint saved = leafCheckpoint();
        consumeInto(line_);  // typedef
        skip_directives();
        bool valid = consumeAnnexRule("interface_port_identifier", line_);
        parseGrammarChildDirectiveLines();
        if (valid && at(TK::OpenBracket)) {
          valid = consumeAnnexRule("constant_bit_select", line_, TK::Dot);
        }
        parseGrammarChildDirectiveLines();
        if (valid && at(TK::Dot)) {
          consumeInto(line_);
        } else {
          valid = false;
        }
        parseGrammarChildDirectiveLines();
        if (valid) {
          valid = consumeAnnexRule("type_identifier", line_);
        }
        parseGrammarChildDirectiveLines();
        if (valid) {
          valid = consumeAnnexRule("type_identifier", line_);
        }
        parseGrammarChildDirectiveLines();
        if (!valid || !at(TK::Semicolon)) {
          recordGrammarFallback("invalid Annex A interface typedef");
          recoverMalformedLeaf(saved);
          return true;
        }
        consumeInto(line_);
        addLine();
        return true;
      }
    }
    size_t identifier_offset = type_start;
    const size_t class_offset = afterOrdinaryDirectives(type_start + 1);
    const bool interface_class = at(TK::InterfaceKeyword, type_start) &&
                                 at(TK::ClassKeyword, class_offset);
    const bool forward =
        annexCanStart("forward_type", peek(type_start).kind) &&
        (!at(TK::InterfaceKeyword, type_start) || interface_class);
    if (forward) {
      identifier_offset = interface_class ? class_offset + 1 : type_start + 1;
    }
    const size_t name_offset = afterOrdinaryDirectives(identifier_offset);
    if (at(TK::Identifier, name_offset) &&
        at(TK::Semicolon, afterOrdinaryDirectives(name_offset + 1))) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);  // typedef
      skip_directives();
      bool valid = !forward || consumeAnnexRule("forward_type", line_);
      skip_directives();
      if (valid) {
        valid = consumeAnnexRule("type_identifier", line_);
      }
      parseGrammarChildDirectiveLines();
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A forward type declaration");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    if (annexCanStart("data_type_or_incomplete_class_scoped_type",
                      peek(type_start).kind)) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);  // typedef
      skip_directives();
      bool valid =
          consumeAnnexRule("data_type_or_incomplete_class_scoped_type", line_);
      parseGrammarChildDirectiveLines();
      if (valid) {
        valid = consumeAnnexRule("type_identifier", line_);
      }
      parseGrammarChildDirectiveLines();
      while (valid && at(TK::OpenBracket)) {
        valid = consumeAnnexRule("variable_dimension", line_);
        parseGrammarChildDirectiveLines();
      }
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A type declaration");
        recoverMalformedLeaf(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    static_cast<void>(parseAnnexItem({"type_declaration"}, true));
    return true;
  }

  auto parseNettypeDeclarationRule() -> bool {
    if (!at(TK::NetTypeKeyword)) {
      return false;
    }
    if (hasAnnexListInterruption(pos_, false)) {
      static_cast<void>(parseAnnexItem({"nettype_declaration"}, true));
      return true;
    }
    const size_t type_start = afterOrdinaryDirectives(1);
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    bool has_resolver = false;
    for (size_t i = pos_ + 1; i < tokens_.size(); ++i) {
      if (isCompilerDirective(tokens_[i]) &&
          !isConditionalStartDirective(tokens_[i]) &&
          !isConditionalBoundaryDirective(tokens_[i])) {
        i = pos_ + afterOrdinaryDirectives(i - pos_) - 1;
        continue;
      }
      if (tokens_[i].kind == TK::Semicolon ||
          tokens_[i].kind == TK::EndOfFile) {
        break;
      }
      if (tokens_[i].kind == TK::WithKeyword) {
        has_resolver = true;
      }
    }
    // An unqualified identifier can begin either Annex A alternative. The
    // resolver suffix or parameterized type selects the data_type alternative;
    // otherwise the alias branch retains the shared spelling. All other type
    // starters come from the imported data_type first set.
    const bool explicit_type =
        annexCanStart("data_type", peek(type_start).kind) &&
        (has_resolver ||
         (at(TK::Identifier, type_start) && at(TK::Hash, type_start + 1)) ||
         (!at(TK::Identifier, type_start) &&
          !at(TK::UnitSystemName, type_start)));
    if (explicit_type) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);  // nettype
      skip_directives();
      bool valid = consumeAnnexRule("data_type", line_);
      parseGrammarChildDirectiveLines();
      if (valid) {
        valid = consumeAnnexRule("nettype_identifier", line_);
      }
      if (!valid) {
        recordGrammarFallback("invalid Annex A nettype declaration");
        recoverMalformedItem(saved);
        return true;
      }
      parseGrammarChildDirectiveLines();
      if (at(TK::WithKeyword)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
        if ((at(TK::Identifier) && at(TK::DoubleColon, 1)) ||
            at(TK::UnitSystemName)) {
          beginGrammar({"package_scope", "class_scope"});
          while (!at(TK::EndOfFile)) {
            const auto& grammar = grammar_scopes_.back();
            // class_scope can also accept the resolver as another class name.
            // The final identifier before ';' belongs to tf_identifier.
            if (grammar.complete() && at(TK::Identifier) &&
                at(TK::Semicolon, 1)) {
              break;
            }
            if (isCompilerDirective(peek())) {
              addLine();
              parseDirectiveLine();
              continue;
            }
            if (grammar.complete() && !grammar.accepts(peek().kind)) {
              break;
            }
            if (!grammar.accepts(peek().kind)) {
              break;
            }
            consumeInto(line_);
          }
          const AnnexState scope = endGrammar(false);
          if (scope.failed || scope.interrupted || !scope.complete()) {
            recordGrammarFallback("invalid Annex A nettype resolver scope");
            recoverMalformedItem(saved);
            return true;
          }
        }
        if (!consumeAnnexRule("tf_identifier", line_)) {
          recordGrammarFallback("invalid Annex A nettype resolver");
          recoverMalformedItem(saved);
          return true;
        }
        parseGrammarChildDirectiveLines();
      }
      if (!at(TK::Semicolon)) {
        recordGrammarFallback("missing Annex A nettype semicolon");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    // The second alternative is a nettype alias. A bare user type has the
    // same two-identifier spelling and follows the same line boundary.
    if (has_resolver || at(TK::Hash, type_start + 1)) {
      static_cast<void>(parseAnnexItem({"nettype_declaration"}, true));
      return true;
    }
    if ((at(TK::Identifier, type_start) &&
         (at(TK::Identifier, type_start + 1) ||
          at(TK::DoubleColon, type_start + 1))) ||
        (at(TK::UnitSystemName, type_start) &&
         at(TK::DoubleColon, type_start + 1))) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);  // nettype
      skip_directives();
      bool valid = true;
      if (at(TK::DoubleColon, 1) || at(TK::UnitSystemName)) {
        beginGrammar({"package_scope", "class_scope"});
        while (!at(TK::EndOfFile)) {
          if (isCompilerDirective(peek())) {
            parseGrammarChildDirectiveLines();
            continue;
          }
          const auto& scope = grammar_scopes_.back();
          if (scope.complete() && at(TK::Identifier) && at(TK::Identifier, 1) &&
              at(TK::Semicolon, 2)) {
            break;
          }
          if (scope.complete() && !scope.accepts(peek().kind)) {
            break;
          }
          if (!scope.accepts(peek().kind)) {
            break;
          }
          consumeInto(line_);
        }
        const AnnexState scope = endGrammar(false);
        valid = !scope.failed && !scope.interrupted && scope.complete();
      }
      parseGrammarChildDirectiveLines();
      if (valid) {
        valid = consumeAnnexRule("nettype_identifier", line_);
      }
      parseGrammarChildDirectiveLines();
      if (valid) {
        valid = consumeAnnexRule("nettype_identifier", line_);
      }
      parseGrammarChildDirectiveLines();
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A nettype alias");
        recoverMalformedLeaf(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    static_cast<void>(parseAnnexItem({"nettype_declaration"}, true));
    return true;
  }

  // param_assignment ::= parameter_identifier { variable_dimension }
  //                      [ '=' constant_param_expression ].
  [[nodiscard]] auto parseParameterAssignmentRule(bool type) -> bool {
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule(type ? "type_identifier" : "parameter_identifier",
                          line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!type) {
      while (at(TK::OpenBracket)) {
        if (!consumeAnnexRule("variable_dimension", line_)) {
          return false;
        }
        parseGrammarChildDirectiveLines();
      }
    }
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule(type ? "data_type_or_incomplete_class_scoped_type"
                                 : "constant_param_expression",
                            line_, TK::Comma, [&] {
                              return at(TK::Semicolon) ||
                                     at(TK::CloseParenthesis);
                            })) {
        return false;
      }
    }
    return true;
  }

  [[nodiscard]] auto parseParameterAssignmentListRule(bool type) -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseParameterAssignmentRule(type)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  auto parseTypeAssignmentListRule() -> bool {
    return parseParameterAssignmentListRule(true);
  }

  // variable_decl_assignment has ordinary, dynamic-array and class-new
  // alternatives. The first unsized dimension and the initializer select
  // their children; a local Annex A candidate resolves qualified class_new.
  [[nodiscard]] auto parseVariableAssignmentRule() -> bool {
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("variable_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    const bool first_unsized = at(TK::OpenBracket) && at(TK::CloseBracket, 1);
    if (first_unsized) {
      if (!consumeAnnexRule("unsized_dimension", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    bool has_dimensions = first_unsized;
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule("variable_dimension", line_)) {
        return false;
      }
      has_dimensions = true;
      parseGrammarChildDirectiveLines();
    }
    if (!at(TK::Equals)) {
      return true;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    const bool dynamic_new =
        first_unsized && at(TK::NewKeyword) && at(TK::OpenBracket, 1);
    bool qualified_new = false;
    if (!has_dimensions && at(TK::Identifier) &&
        (at(TK::DoubleColon, 1) || at(TK::Hash, 1))) {
      AnnexState candidate({"class_new"});
      bool saw_new = false;
      for (size_t offset = 0; pos_ + offset < tokens_.size(); ++offset) {
        if (isCompilerDirective(peek(offset)) ||
            !candidate.accepts(peek(offset).kind)) {
          break;
        }
        saw_new |= at(TK::NewKeyword, offset);
        candidate.advance(peek(offset));
        if (saw_new && candidate.complete() &&
            (at(TK::Comma, offset + 1) || at(TK::Semicolon, offset + 1))) {
          qualified_new = true;
          break;
        }
      }
    }
    const std::string_view initializer =
        dynamic_new ? "dynamic_array_new"
        : (!has_dimensions && (at(TK::NewKeyword) || qualified_new))
            ? "class_new"
            : "expression";
    return consumeAnnexRule(initializer, line_, TK::Comma,
                            [&] { return at(TK::Semicolon); });
  }

  [[nodiscard]] auto parseVariableAssignmentItemsRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseVariableAssignmentRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  auto parseVariableAssignmentListRule(bool conditional_members) -> bool {
    return conditional_members ? parseConditionalAnnexCommaListRule(
                                     "list_of_variable_decl_assignments",
                                     "variable_decl_assignment")
                               : parseVariableAssignmentItemsRule();
  }

  // net_decl_assignment ::= net_identifier { unpacked_dimension }
  // [ '=' expression ].
  [[nodiscard]] auto parseNetAssignmentRule() -> bool {
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("net_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule("unpacked_dimension", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("expression", line_, TK::Comma,
                            [&] { return at(TK::Semicolon); })) {
        return false;
      }
    }
    return true;
  }

  [[nodiscard]] auto parseNetAssignmentItemsRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseNetAssignmentRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  auto parseNetAssignmentListRule(bool conditional_members) -> bool {
    return conditional_members
               ? parseConditionalAnnexCommaListRule(
                     "list_of_net_decl_assignments", "net_decl_assignment")
               : parseNetAssignmentItemsRule();
  }

  auto parseParameterDeclarationRule() -> bool {
    if (!at(TK::ParameterKeyword) && !at(TK::LocalParamKeyword)) {
      return false;
    }
    const size_t type_start = afterOrdinaryDirectives(1);
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    if (at(TK::TypeKeyword, type_start)) {
      const bool conditional_members = hasConditionalListMember(pos_);
      const bool interrupted =
          hasAnnexListInterruption(pos_, conditional_members);
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);  // parameter / localparam
      skip_directives();
      if (interrupted) {
        if (!consumeAnnexRule("type_parameter_declaration", line_,
                              TK::Semicolon) ||
            !at(TK::Semicolon)) {
          recordGrammarFallback("invalid Annex A type parameter declaration");
          recoverMalformedItem(saved);
          return true;
        }
        consumeInto(line_);
        addLine();
        return true;
      }
      consumeInto(line_);  // type
      skip_directives();
      const bool forward = annexCanStart("forward_type", peek().kind) &&
                           (!at(TK::InterfaceKeyword) ||
                            at(TK::ClassKeyword, afterOrdinaryDirectives(1)));
      bool valid = !forward || consumeAnnexRule("forward_type", line_);
      skip_directives();
      if (!valid ||
          !(conditional_members
                ? parseConditionalAnnexCommaListRule("list_of_type_assignments",
                                                     "type_assignment")
                : parseTypeAssignmentListRule()) ||
          !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A type parameter declaration");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    const auto declaration = at(TK::ParameterKeyword)
                                 ? "parameter_declaration"
                                 : "local_parameter_declaration";
    const auto after_identifier = at(TK::Identifier, type_start)
                                      ? afterBalancedDimensions(type_start + 1)
                                      : std::optional<size_t>{type_start + 1};
    if (!after_identifier) {
      parseAnnexSemicolonItem(declaration);
      return true;
    }
    const size_t boundary = afterOrdinaryDirectives(*after_identifier);
    const bool explicit_type =
        (at(TK::Identifier, type_start) &&
         (at(TK::Identifier, boundary) || at(TK::DoubleColon, boundary) ||
          at(TK::Hash, boundary))) ||
        (annexCanStart("data_type", peek(type_start).kind) &&
         !at(TK::Identifier, type_start) &&
         !at(TK::SignedKeyword, type_start) &&
         !at(TK::UnsignedKeyword, type_start) &&
         !at(TK::OpenBracket, type_start));
    const bool implicit_type = at(TK::SignedKeyword, type_start) ||
                               at(TK::UnsignedKeyword, type_start) ||
                               at(TK::OpenBracket, type_start);
    const bool bare_assignment =
        at(TK::Identifier, type_start) &&
        (at(TK::Equals, boundary) || at(TK::Comma, boundary) ||
         at(TK::Semicolon, boundary));
    if (!explicit_type && !implicit_type && !bare_assignment) {
      parseAnnexSemicolonItem(declaration);
      return true;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    if (hasAnnexListInterruption(pos_, conditional_members)) {
      parseAnnexSemicolonItem(declaration);
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // parameter / localparam
    skip_directives();
    const std::string_view type_rule = explicit_type   ? "data_type_or_implicit"
                                       : implicit_type ? "implicit_data_type"
                                                       : "";
    if ((!type_rule.empty() && !consumeAnnexRule(type_rule, line_)) ||
        !(conditional_members
              ? parseConditionalAnnexCommaListRule("list_of_param_assignments",
                                                   "param_assignment")
              : parseParameterAssignmentListRule(false)) ||
        !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A parameter declaration");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // A user type, optionally scoped and packed, precedes the first Annex A
  // variable_decl_assignment. Instance-shaped pairs are handled earlier by
  // the instantiation production in contexts where it is permitted.
  auto parseUserDataDeclarationRule() -> bool {
    if (!at(TK::Identifier) && !at(TK::UnitSystemName)) {
      return false;
    }
    size_t type_identifier = 0;
    if (at(TK::UnitSystemName)) {
      if (!at(TK::DoubleColon, 1) || !at(TK::Identifier, 2)) {
        return false;
      }
      type_identifier = 2;
    }
    const auto variable = afterUserTypePrefix(type_identifier);
    const size_t variable_offset =
        variable ? afterOrdinaryDirectives(*variable) : 0;
    if (!variable || !at(TK::Identifier, variable_offset) ||
        at(TK::OpenParenthesis, variable_offset + 1)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const bool conditional_members = hasConditionalListMember(pos_);
    const bool interrupted =
        hasAnnexListInterruption(pos_, conditional_members);
    if (!consumeAnnexRule("data_type_or_implicit", line_) ||
        !(interrupted ? consumeAnnexRule("list_of_variable_decl_assignments",
                                         line_, TK::Semicolon)
                      : parseVariableAssignmentListRule(conditional_members)) ||
        !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A user-typed declaration");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseExplicitDataDeclarationRule() -> bool {
    if (!annexCanStart("data_type_or_implicit", peek().kind) ||
        at(TK::Identifier) ||
        (at(TK::UnitSystemName) &&
         !(at(TK::DoubleColon, 1) && at(TK::Identifier, 2) &&
           at(TK::Identifier, 3)))) {
      return false;
    }
    if (at(TK::VirtualKeyword) &&
        (at(TK::ClassKeyword, 1) || at(TK::FunctionKeyword, 1) ||
         at(TK::TaskKeyword, 1))) {
      return false;
    }
    if (at(TK::TypeKeyword) && !at(TK::OpenParenthesis, 1)) {
      return false;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    if (hasAnnexListInterruption(pos_, conditional_members)) {
      static_cast<void>(parseAnnexItem({"data_declaration"}, true));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    if (!consumeAnnexRule("data_type_or_implicit", line_) ||
        !parseVariableAssignmentListRule(conditional_members) ||
        !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A built-in data declaration");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseQualifiedDataDeclarationRule() -> bool {
    if (!at(TK::ConstKeyword) && !at(TK::VarKeyword) &&
        !at(TK::StaticKeyword) && !at(TK::AutomaticKeyword)) {
      return false;
    }
    size_t offset = 0;
    if (at(TK::ConstKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    if (at(TK::VarKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    if (at(TK::StaticKeyword, offset) || at(TK::AutomaticKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    const TK type_start = peek(offset).kind;
    const auto after_identifier = type_start == TK::Identifier
                                      ? afterBalancedDimensions(offset + 1)
                                      : std::optional<size_t>{offset + 1};
    if (!after_identifier) {
      return false;
    }
    const size_t boundary = afterOrdinaryDirectives(*after_identifier);
    const bool implicit_type =
        type_start == TK::Identifier &&
        (at(TK::Semicolon, boundary) || at(TK::Equals, boundary) ||
         at(TK::Comma, boundary));
    if (!annexCanStart("data_type_or_implicit", type_start)) {
      return false;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    if (hasAnnexListInterruption(pos_, conditional_members)) {
      static_cast<void>(parseAnnexItem({"data_declaration"}, true));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    if (at(TK::ConstKeyword)) {
      consumeInto(line_);
      skip_directives();
    }
    if (at(TK::VarKeyword)) {
      consumeInto(line_);
      skip_directives();
    }
    bool valid = true;
    if (at(TK::StaticKeyword) || at(TK::AutomaticKeyword)) {
      valid = consumeAnnexRule("lifetime", line_);
      skip_directives();
    }
    if (valid && !implicit_type) {
      valid = consumeAnnexRule("data_type_or_implicit", line_);
    }
    if (valid) {
      valid = parseVariableAssignmentListRule(conditional_members);
    }
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A qualified data declaration");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseNetDeclarationRule() -> bool {
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    if (at(TK::InterconnectKeyword)) {
      for (size_t i = pos_; i < tokens_.size(); ++i) {
        const auto& token = tokens_[i];
        if (isConditionalStartDirective(token) ||
            token.kind == TK::MacroUsage ||
            (token.kind == TK::Directive && !isCompilerDirective(token))) {
          static_cast<void>(parseAnnexItem({"net_declaration"}, true));
          return true;
        }
        if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
          break;
        }
      }
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);
      skip_directives();
      bool valid = true;
      if (at(TK::SignedKeyword) || at(TK::UnsignedKeyword)) {
        valid = consumeAnnexRule("signing", line_);
      }
      skip_directives();
      while (valid && at(TK::OpenBracket)) {
        valid = consumeAnnexRule("packed_dimension", line_);
        skip_directives();
      }
      if (valid && at(TK::Hash)) {
        consumeInto(line_);
        skip_directives();
        valid = consumeAnnexRule("delay_value", line_);
        skip_directives();
      }
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        if (valid) {
          valid = consumeAnnexRule("net_identifier", line_);
        }
        skip_directives();
        while (valid && at(TK::OpenBracket)) {
          valid = consumeAnnexRule("unpacked_dimension", line_);
          skip_directives();
        }
        if (!valid || !at(TK::Comma)) {
          break;
        }
        consumeInto(line_);
        skip_directives();
      } while (true);
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A interconnect declaration");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    if (!annexCanStart("net_type", peek().kind)) {
      return false;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    bool ambiguous = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if ((isConditionalStartDirective(token) && !conditional_members) ||
          token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        ambiguous = true;
        break;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    if (ambiguous) {
      static_cast<void>(parseAnnexItem({"net_declaration"}, true));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = consumeAnnexRule("net_type", line_);
    skip_directives();
    if (valid && at(TK::OpenParenthesis)) {
      const bool charge = at(TK::SmallKeyword, 1) || at(TK::MediumKeyword, 1) ||
                          at(TK::LargeKeyword, 1);
      valid = consumeAnnexRule(charge ? "charge_strength" : "drive_strength",
                               line_);
      skip_directives();
    }
    if (valid && (at(TK::VectoredKeyword) || at(TK::ScalaredKeyword))) {
      consumeInto(line_);
      skip_directives();
    }
    // A complete user type prefix followed by a second identifier selects
    // the data_type child. Dimensions on the first identifier alone belong
    // to the net_decl_assignment after an implicit type.
    const auto after_type =
        at(TK::Identifier) ? afterUserTypePrefix(0) : std::nullopt;
    const bool user_type =
        (after_type &&
         at(TK::Identifier, afterOrdinaryDirectives(*after_type))) ||
        (at(TK::UnitSystemName) && at(TK::DoubleColon, 1));
    if (valid && annexCanStart("data_type_or_implicit", peek().kind) &&
        (user_type || (!at(TK::Identifier) && !at(TK::UnitSystemName)))) {
      valid = consumeAnnexRule(
          "data_type_or_implicit", line_, std::nullopt,
          [&] { return at(TK::Hash) && !at(TK::OpenParenthesis, 1); });
    }
    skip_directives();
    if (valid && at(TK::Hash)) {
      valid = consumeAnnexRule("delay3", line_);
    }
    skip_directives();
    if (valid) {
      valid = parseNetAssignmentListRule(conditional_members);
    }
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A net declaration");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // dpi_import_export has a string after import/export. Package imports and
  // exports instead begin with a package identifier or '*'.
  auto parseDpiDeclarationRule() -> bool {
    if ((!at(TK::ImportKeyword) && !at(TK::ExportKeyword)) ||
        !at(TK::StringLiteral, afterOrdinaryDirectives(1))) {
      return false;
    }
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        static_cast<void>(parseAnnexItem({"dpi_import_export"}, true));
        return true;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const bool import = at(TK::ImportKeyword);
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    consumeInto(line_);
    skip_directives();
    const auto spec = peek().rawText();
    bool valid = (spec == "\"DPI-C\"" || spec == "\"DPI\"") &&
                 consumeAnnexRule("dpi_spec_string", line_);
    skip_directives();
    const bool pure = at(TK::PureKeyword);
    if (valid && import && (at(TK::ContextKeyword) || at(TK::PureKeyword))) {
      valid = consumeAnnexRule(at(TK::ContextKeyword)
                                   ? "dpi_task_import_property"
                                   : "dpi_function_import_property",
                               line_);
    }
    skip_directives();
    if (valid && at(TK::Identifier) &&
        at(TK::Equals, afterOrdinaryDirectives(1))) {
      // c_identifier is a character-level Annex A lexical production. slang
      // has already combined it into a token, so check that token's lexeme.
      const auto name = peek().rawText();
      const auto letter = [](char ch) {
        return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
               ch == '_';
      };
      valid = !name.empty() && letter(name.front());
      for (size_t i = 1; valid && i < name.size(); ++i) {
        valid = letter(name.at(i)) || (name.at(i) >= '0' && name.at(i) <= '9');
      }
      if (valid) {
        consumeInto(line_);
        skip_directives();
        consumeInto(line_);  // '='
        skip_directives();
      }
    }
    if (valid && import) {
      if (at(TK::FunctionKeyword)) {
        valid = consumeAnnexRule("dpi_function_proto", line_, TK::Semicolon);
      } else if (at(TK::TaskKeyword)) {
        valid =
            !pure && consumeAnnexRule("dpi_task_proto", line_, TK::Semicolon);
      } else {
        valid = false;
      }
    } else if (valid) {
      if (at(TK::FunctionKeyword)) {
        consumeInto(line_);
        valid = consumeAnnexRule("function_identifier", line_);
      } else if (at(TK::TaskKeyword)) {
        consumeInto(line_);
        valid = consumeAnnexRule("task_identifier", line_);
      } else {
        valid = false;
      }
    }
    skip_directives();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A DPI declaration");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // Keep a declaration with a comma-separated child list active through
  // conditional branches, including its own trailing semicolon.
  auto parseConditionalAnnexDeclarationListRule(
      std::string_view declaration, const std::function<bool()>& parse_child)
      -> bool {
    beginGrammar({declaration});
    bool valid = grammarAllows(peek().kind);
    if (valid) {
      consumeInto(line_);
    }
    bool ended = false;
    while (valid && !at(TK::EndOfFile) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        valid =
            parseAnnexConditional(TK::EndOfFile, header_ended, indent_level_);
      } else if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      } else if (at(TK::Semicolon)) {
        valid = grammarAllows(TK::Semicolon);
        if (valid) {
          consumeInto(line_);
          ended = true;
        }
        break;
      } else if (at(TK::Comma)) {
        valid = grammarAllows(TK::Comma);
        if (valid) {
          consumeInto(line_);
        }
      } else {
        valid = grammarAllows(peek().kind) && parse_child();
      }
      if (grammar_scopes_.back().failed || grammar_scopes_.back().interrupted) {
        valid = false;
      }
    }
    const AnnexState result = endGrammar(false);
    return valid && ended && !result.failed && !result.interrupted &&
           result.complete();
  }

  // package_import_item ::= package_identifier '::' identifier |
  //                         package_identifier '::' '*'.
  [[nodiscard]] auto parsePackageImportItemRule() -> bool {
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("package_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::DoubleColon)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (at(TK::Star)) {
      consumeInto(line_);
      return true;
    }
    // Annex A's identifier is a lexical nonterminal; slang has already
    // produced its complete Identifier token.
    if (!at(TK::Identifier)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  [[nodiscard]] auto parseHeaderPackageImportRule() -> bool {
    if (!at(TK::ImportKeyword)) {
      return false;
    }
    consumeInto(line_);
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parsePackageImportItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    if (!at(TK::Semicolon)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  auto parsePackageImportExportRule() -> bool {
    if ((!at(TK::ImportKeyword) && !at(TK::ExportKeyword)) ||
        at(TK::StringLiteral, afterOrdinaryDirectives(1))) {
      return false;
    }
    const bool import = at(TK::ImportKeyword);
    const auto rule =
        import ? "package_import_declaration" : "package_export_declaration";
    const bool conditional_members = hasConditionalListMember(pos_);
    if (conditional_members &&
        !hasAnnexListInterruption(pos_, conditional_members)) {
      const LeafCheckpoint saved = leafCheckpoint();
      if (!parseConditionalAnnexDeclarationListRule(
              rule, [&] { return parsePackageImportItemRule(); })) {
        recordGrammarFallback("invalid Annex A conditional package items");
        recoverMalformedLeaf(saved);
      } else {
        addLine();
      }
      return true;
    }
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token)) {
        static_cast<void>(parseAnnexItem({rule}, true));
        return true;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    bool valid = true;
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (!import && at(TK::Star)) {
      consumeInto(line_);
      skip_directives();
      if (at(TK::DoubleColon)) {
        consumeInto(line_);
      } else {
        valid = false;
      }
      skip_directives();
      if (valid && at(TK::Star)) {
        consumeInto(line_);
      } else {
        valid = false;
      }
    } else {
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        if (at(TK::Comma)) {
          consumeInto(line_);
        }
        valid = parsePackageImportItemRule();
        skip_directives();
      } while (valid && at(TK::Comma));
    }
    skip_directives();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A package import or export");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // package_or_generate_item_declaration alternatives whose first terminal
  // identifies the declaration. Shared prefixes still use the local grammar.
  auto parsePackageOrGenerateDeclarationRule() -> bool {
    if (at(TK::Semicolon)) {
      consumeInto(line_);
      addLine();
      return true;
    }
    if (parseClassConstructorRule()) {
      return true;
    }
    if (parseQualifiedDataDeclarationRule()) {
      return true;
    }
    if (parseDpiDeclarationRule()) {
      return true;
    }
    if (at(TK::ImportKeyword) || at(TK::ExportKeyword)) {
      return parsePackageImportExportRule();
    }
    if (at(TK::ConstraintKeyword) ||
        (at(TK::StaticKeyword) &&
         at(TK::ConstraintKeyword, afterOrdinaryDirectives(1)))) {
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
        parseCheckerBlockRule();
        return true;
      case TK::ClassKeyword:
        parseNamedBlock(TK::EndClassKeyword);
        return true;
      case TK::InterfaceKeyword:
        if (!at(TK::ClassKeyword, 1)) {
          return false;
        }
        parseNamedBlock(TK::EndClassKeyword);
        return true;
      case TK::CoverGroupKeyword:
        parseCovergroupBlockRule();
        return true;
      case TK::PropertyKeyword:
        parseAnnexWholeBlock(TK::EndPropertyKeyword, "property_declaration");
        return true;
      case TK::SequenceKeyword:
        parseAnnexWholeBlock(TK::EndSequenceKeyword, "sequence_declaration");
        return true;
      case TK::LetKeyword:
        return parseLetDeclarationRule();
      default:
        return false;
    }
  }

  // The two 'default clocking' productions differ after the identifier:
  // a declaration has clocking_event, while the selection ends at ';'.
  auto parseDefaultClockingOrDisableRule(bool checker) -> bool {
    if (!at(TK::DefaultKeyword) ||
        (!at(TK::ClockingKeyword, 1) && !at(TK::DisableKeyword, 1))) {
      return false;
    }
    const std::string_view declaration =
        checker ? "checker_or_generate_item_declaration"
                : "module_or_generate_item_declaration";
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        static_cast<void>(parseAnnexItem({declaration}, true));
        return true;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // default
    const bool clocking = at(TK::ClockingKeyword);
    consumeInto(line_);  // clocking / disable
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (!clocking) {
      if (!at(TK::IffKeyword)) {
        recordGrammarFallback("invalid Annex A default disable iff");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      if (!consumeAnnexRule("expression_or_dist", line_, TK::Semicolon) ||
          !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A default disable condition");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    const bool has_identifier = at(TK::Identifier);
    if (has_identifier) {
      if (!consumeAnnexRule("clocking_identifier", line_)) {
        recordGrammarFallback("invalid Annex A default clocking identifier");
        recoverMalformedItem(saved);
        return true;
      }
      skip_directives();
    }
    const bool declaration_header = at(TK::At);
    if (declaration_header && !consumeAnnexRule("clocking_event", line_)) {
      recordGrammarFallback("invalid Annex A default clocking event");
      recoverMalformedItem(saved);
      return true;
    }
    if (!at(TK::Semicolon) || (!declaration_header && !has_identifier)) {
      recordGrammarFallback("invalid Annex A default clocking header");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    if (declaration_header) {
      parseDelimitedBody(TK::EndClockingKeyword, "clocking_item");
    }
    return true;
  }

  auto parseClockingDeclarationRule() -> bool {
    if (!at(TK::ClockingKeyword) &&
        !(at(TK::GlobalKeyword) && at(TK::ClockingKeyword, 1))) {
      return false;
    }
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage) {
        parseAnnexDelimitedBlock(TK::EndClockingKeyword, "clocking_declaration",
                                 "clocking_item");
        return true;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const bool global = at(TK::GlobalKeyword);
    if (global) {
      consumeInto(line_);
    }
    consumeInto(line_);  // clocking
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (at(TK::Identifier)) {
      if (!consumeAnnexRule("clocking_identifier", line_)) {
        recordGrammarFallback("invalid Annex A clocking identifier");
        recoverMalformedItem(saved);
        return true;
      }
      skip_directives();
    }
    if (!consumeAnnexRule("clocking_event", line_) || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A clocking header");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    if (global) {
      pushOpenFrame(TK::EndClockingKeyword);
      ++indent_level_;
      while (isCompilerDirective(peek())) {
        parseDirectiveLine();
      }
      if (!at(TK::EndClockingKeyword)) {
        recordGrammarFallback("global clocking has no clocking_item body");
        emitOpaque(pos_, findOuterBoundary(pos_));
      }
      if (at(TK::EndClockingKeyword)) {
        parseOpenFrameClose();
      }
    } else {
      parseDelimitedBody(TK::EndClockingKeyword, "clocking_item");
    }
    return true;
  }

  // checker_port_item ::= { attribute_instance } [ direction ]
  //   property_formal_type formal_port_identifier { variable_dimension }
  //   [ '=' property_actual_arg ].
  [[nodiscard]] auto parseCheckerPortItemRule() -> bool {
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::InputKeyword) || at(TK::OutputKeyword)) {
      if (!consumeAnnexRule("checker_port_direction", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    const bool implicit_type =
        implicitIdentifierBefore({TK::Comma, TK::CloseParenthesis, TK::Equals});
    if (!implicit_type && !consumeAnnexRule("property_formal_type", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("formal_port_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule("variable_dimension", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("property_actual_arg", line_, TK::Comma,
                            [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    return true;
  }

  [[nodiscard]] auto parseCheckerPortListRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseCheckerPortItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // property_port_item / sequence_port_item. Their formal type may be the
  // empty data_type_or_implicit production; in that case the first identifier
  // is the port name, followed only by dimensions and an optional default.
  [[nodiscard]] auto parseAssertionPortItemRule(bool property) -> bool {
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::LocalKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (at(TK::InputKeyword) ||
          (!property && (at(TK::InOutKeyword) || at(TK::OutputKeyword)))) {
        if (!consumeAnnexRule(property ? "property_lvar_port_direction"
                                       : "sequence_lvar_port_direction",
                              line_)) {
          return false;
        }
        parseGrammarChildDirectiveLines();
      }
    }
    const bool implicit_type =
        implicitIdentifierBefore({TK::Comma, TK::CloseParenthesis, TK::Equals});
    if (!implicit_type && !consumeAnnexRule(property ? "property_formal_type"
                                                     : "sequence_formal_type",
                                            line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("formal_port_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule("variable_dimension", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule(
              property ? "property_actual_arg" : "sequence_actual_arg", line_,
              TK::Comma, [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    return true;
  }

  [[nodiscard]] auto parseAssertionPortListRule(bool property) -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseAssertionPortItemRule(property)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // tf_port_direction ::= port_direction | [ const ] ref [ static ].
  // Consume the optional static after directive lines in the same child rule.
  [[nodiscard]] auto parseTfPortDirectionRule() -> bool {
    if (at(TK::ConstKeyword) || at(TK::RefKeyword)) {
      if (at(TK::ConstKeyword)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
      }
      if (!at(TK::RefKeyword)) {
        return false;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (at(TK::StaticKeyword)) {
        consumeInto(line_);
      }
      return true;
    }
    return consumeAnnexRule("port_direction", line_);
  }

  // tf_port_item ::= { attribute_instance } [ tf_port_direction ] [ var ]
  // data_type_or_implicit [ port_identifier { variable_dimension }
  // [ '=' expression ] ].
  [[nodiscard]] auto parseTfPortItemRule() -> bool {
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::InputKeyword) || at(TK::OutputKeyword) || at(TK::InOutKeyword) ||
        at(TK::RefKeyword) || at(TK::ConstKeyword)) {
      if (!parseTfPortDirectionRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::VarKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
    }
    const bool implicit_type =
        implicitIdentifierBefore({TK::Comma, TK::CloseParenthesis, TK::Equals});
    if (!implicit_type && !consumeAnnexRule("data_type_or_implicit", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (at(TK::Identifier)) {
      if (!consumeAnnexRule("port_identifier", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      while (at(TK::OpenBracket)) {
        if (!consumeAnnexRule("variable_dimension", line_)) {
          return false;
        }
        parseGrammarChildDirectiveLines();
      }
      if (at(TK::Equals)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
        if (!consumeAnnexRule("expression", line_, TK::Comma,
                              [&] { return at(TK::CloseParenthesis); })) {
          return false;
        }
      }
    }
    return true;
  }

  [[nodiscard]] auto parseTfPortListRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseTfPortItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // class_constructor_arg ::= tf_port_item | default.
  [[nodiscard]] auto parseClassConstructorArgListRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      parseGrammarChildDirectiveLines();
      if (at(TK::DefaultKeyword)) {
        consumeInto(line_);
      } else if (!parseTfPortItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // checker_declaration ::= checker checker_identifier
  // [ '(' [ checker_port_list ] ')' ] ';' { checker_or_generate_item }
  // endchecker [ ':' checker_identifier ].
  auto parseCheckerBlockRule() -> void {
    const size_t identifier = afterOrdinaryDirectives(1);
    const size_t ports = afterOrdinaryDirectives(identifier + 1);
    const bool conditional_ports =
        at(TK::Identifier, identifier) && at(TK::OpenParenthesis, ports) &&
        hasConditionalListMember(pos_ + ports + 1, TK::CloseParenthesis);
    if (hasAnnexHeaderInterruption(pos_, conditional_ports)) {
      parseAnnexDelimitedBlock(TK::EndCheckerKeyword, "checker_declaration",
                               "checker_or_generate_item");
      return;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // checker
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (!consumeAnnexRule("checker_identifier", line_)) {
      recordGrammarFallback("invalid Annex A checker identifier");
      recoverMalformedItem(saved);
      return;
    }
    skip_directives();
    if (at(TK::OpenParenthesis)) {
      consumeInto(line_);
      bool valid = true;
      if (!at(TK::CloseParenthesis)) {
        valid = conditional_ports
                    ? parseConditionalAnnexCommaListRule("checker_port_list",
                                                         "checker_port_item",
                                                         TK::CloseParenthesis)
                    : parseCheckerPortListRule();
      }
      if (!valid || !at(TK::CloseParenthesis)) {
        recordGrammarFallback("invalid Annex A checker port list");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      skip_directives();
    }
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A checker semicolon");
      recoverMalformedItem(saved);
      return;
    }
    consumeInto(line_);
    addLine();
    parseDelimitedBody(TK::EndCheckerKeyword, "checker_or_generate_item");
  }

  // coverage_event ::= clocking_event | with function sample '(' [ tf_port_list
  // ]
  // ')' | '@@' '(' block_event_expression ')'.
  [[nodiscard]] auto parseCoverageEventRule() -> bool {
    parseGrammarChildDirectiveLines();
    if (at(TK::At)) {
      return consumeAnnexRule("clocking_event", line_);
    }
    if (at(TK::DoubleAt)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      return consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                   "block_event_expression", line_);
    }
    if (!at(TK::WithKeyword)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!at(TK::FunctionKeyword)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (peek().rawText() != "sample") {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis) && !parseTfPortListRule()) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  auto parseCovergroupBlockRule() -> void {
    const size_t header_start = afterOrdinaryDirectives(1);
    const bool extends = at(TK::ExtendsKeyword, header_start);
    const size_t identifier =
        afterOrdinaryDirectives(header_start + (extends ? 1 : 0));
    const size_t ports = afterOrdinaryDirectives(identifier + 1);
    const bool conditional_ports =
        !extends && at(TK::Identifier, identifier) &&
        at(TK::OpenParenthesis, ports) &&
        hasConditionalListMember(pos_ + ports + 1, TK::CloseParenthesis);
    if (hasAnnexHeaderInterruption(pos_, conditional_ports)) {
      parseAnnexDelimitedBlock(TK::EndGroupKeyword, "covergroup_declaration",
                               "coverage_spec_or_option");
      return;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // covergroup
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (extends) {
      consumeInto(line_);
      skip_directives();
    }
    if (!consumeAnnexRule("covergroup_identifier", line_)) {
      recordGrammarFallback("invalid Annex A covergroup identifier");
      recoverMalformedItem(saved);
      return;
    }
    skip_directives();
    if (!extends && at(TK::OpenParenthesis)) {
      consumeInto(line_);
      bool valid = true;
      if (!at(TK::CloseParenthesis)) {
        valid = conditional_ports
                    ? parseConditionalAnnexCommaListRule(
                          "tf_port_list", "tf_port_item", TK::CloseParenthesis)
                    : parseTfPortListRule();
      }
      if (!valid || !at(TK::CloseParenthesis)) {
        recordGrammarFallback("invalid Annex A covergroup port list");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      skip_directives();
    }
    if (!extends && (at(TK::At) || at(TK::DoubleAt) || at(TK::WithKeyword))) {
      if (!parseCoverageEventRule()) {
        recordGrammarFallback("invalid Annex A coverage event");
        recoverMalformedItem(saved);
        return;
      }
      skip_directives();
    }
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A covergroup semicolon");
      recoverMalformedItem(saved);
      return;
    }
    consumeInto(line_);
    addLine();
    parseDelimitedBody(TK::EndGroupKeyword, "coverage_spec_or_option");
  }

  // class_constructor_declaration has its own header and body production.
  // A local Annex A prefix distinguishes 'function new' and
  // 'function class_scope new' from function_declaration.
  auto parseClassConstructorRule() -> bool {
    if (!at(TK::FunctionKeyword)) {
      return false;
    }
    bool constructor_name = at(TK::NewKeyword, afterOrdinaryDirectives(1));
    if (!constructor_name) {
      const auto scope_end = afterUserTypePrefix(afterOrdinaryDirectives(1));
      if (scope_end) {
        const size_t separator = afterOrdinaryDirectives(*scope_end);
        constructor_name =
            at(TK::DoubleColon, separator) &&
            at(TK::NewKeyword, afterOrdinaryDirectives(separator + 1));
      }
    }
    if (!constructor_name) {
      AnnexState candidate({"class_constructor_declaration"});
      for (size_t offset = 0; pos_ + offset < tokens_.size(); ++offset) {
        const TK kind = peek(offset).kind;
        if (isCompilerDirective(peek(offset)) || !candidate.accepts(kind)) {
          break;
        }
        candidate.advance(peek(offset));
        if (kind == TK::NewKeyword &&
            candidate.hasViableRule("class_constructor_declaration")) {
          constructor_name = true;
          break;
        }
        if (kind == TK::Semicolon) {
          break;
        }
      }
    }
    if (!constructor_name) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // function
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    bool valid = true;
    if (!at(TK::NewKeyword)) {
      valid = consumeAnnexRule("class_scope", line_, TK::NewKeyword);
      skip_directives();
    }
    if (valid && at(TK::NewKeyword)) {
      consumeInto(line_);
    } else {
      valid = false;
    }
    skip_directives();
    if (valid && at(TK::OpenParenthesis)) {
      consumeInto(line_);
      skip_directives();
      if (!at(TK::CloseParenthesis)) {
        const bool conditional_members =
            hasConditionalListMember(pos_, TK::CloseParenthesis);
        valid = hasAnnexListInterruption(pos_, conditional_members,
                                         TK::CloseParenthesis)
                    ? consumeAnnexRule("class_constructor_arg_list", line_,
                                       TK::CloseParenthesis)
                : conditional_members
                    ? parseConditionalAnnexCommaListRule(
                          "class_constructor_arg_list", "class_constructor_arg",
                          TK::CloseParenthesis)
                    : parseClassConstructorArgListRule();
      }
      skip_directives();
      if (valid && at(TK::CloseParenthesis)) {
        consumeInto(line_);
      } else {
        valid = false;
      }
    }
    skip_directives();
    if (valid && at(TK::Semicolon)) {
      consumeInto(line_);
      addLine();
    } else {
      recordGrammarFallback("invalid Annex A class constructor header");
      lines_.resize(saved.output_size);
      line_ = saved.line;
      preserved_source_end_ = saved.preserved_source_end;
      indent_level_ = saved.indent_level;
      const auto after = findPairedEnd(saved.pos, TK::EndFunctionKeyword);
      emitOpaque(saved.pos, after ? *after : findOuterBoundary(saved.pos));
      return true;
    }
    parseDelimitedBody(TK::EndFunctionKeyword, {}, true);
    return true;
  }

  // class_constructor_declaration places its optional super.new call after
  // block_item_declaration and before function_statement_or_null.
  auto parseConstructorSuperRule() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    if (block_stack_.back().statement_phase) {
      recordGrammarFallback("super.new outside Annex A constructor position");
      recoverMalformedItem(saved);
      return;
    }
    if (hasAnnexHeaderInterruption(pos_, false)) {
      const std::string_view rule = annexConstructorSuperRule();
      if (rule.empty()) {
        recordGrammarFallback(
            "constructor super production absent from Annex A");
        recoverMalformedItem(saved);
        return;
      }
      beginGrammar({rule});
      parseGrammarLeaf(true, saved, true);
      const AnnexState call = endGrammar();
      if (!call.failed && !call.interrupted && call.complete()) {
        block_stack_.back().statement_phase = true;
      }
      return;
    }
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    consumeInto(line_);  // super
    skip_directives();
    bool valid = at(TK::Dot);
    if (valid) {
      consumeInto(line_);
    }
    skip_directives();
    valid = valid && at(TK::NewKeyword);
    if (valid) {
      consumeInto(line_);
    }
    skip_directives();
    if (valid && at(TK::OpenParenthesis)) {
      consumeInto(line_);
      skip_directives();
      if (at(TK::DefaultKeyword)) {
        consumeInto(line_);
      } else if (!at(TK::CloseParenthesis)) {
        valid =
            consumeAnnexRule("list_of_arguments", line_, TK::CloseParenthesis);
      }
      skip_directives();
      valid = valid && at(TK::CloseParenthesis);
      if (valid) {
        consumeInto(line_);
      }
    }
    skip_directives();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A constructor super call");
      recoverMalformedItem(saved);
      return;
    }
    consumeInto(line_);
    addLine();
    block_stack_.back().statement_phase = true;
  }

  // class_property ::= 'const' { class_item_qualifier } data_type
  //                    const_identifier [ '=' constant_expression ] ';'.
  // A qualifier after const identifies this alternative; unqualified const
  // also begins data_declaration and stays with that alternative's parser.
  auto parseQualifiedConstClassPropertyRule() -> bool {
    const size_t qualifier_start = afterOrdinaryDirectives(1);
    if (!at(TK::ConstKeyword) || (!at(TK::StaticKeyword, qualifier_start) &&
                                  !at(TK::ProtectedKeyword, qualifier_start) &&
                                  !at(TK::LocalKeyword, qualifier_start))) {
      return false;
    }
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        static_cast<void>(parseAnnexItem({"class_property"}, true));
        return true;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    consumeInto(line_);  // const
    skip_directives();
    bool valid = true;
    while (valid && (at(TK::StaticKeyword) || at(TK::ProtectedKeyword) ||
                     at(TK::LocalKeyword))) {
      valid = consumeAnnexRule("class_item_qualifier", line_);
      skip_directives();
    }
    if (valid) {
      valid = consumeAnnexRule("data_type", line_);
    }
    if (valid) {
      valid = consumeAnnexRule("const_identifier", line_);
    }
    skip_directives();
    if (valid && at(TK::Equals)) {
      consumeInto(line_);
      valid = consumeAnnexRule("constant_expression", line_, TK::Semicolon);
    }
    skip_directives();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A qualified const property");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseExplicitClassPropertyRule() -> bool {
    size_t offset = 0;
    while (at(TK::RandKeyword, offset) || at(TK::RandCKeyword, offset) ||
           at(TK::StaticKeyword, offset) || at(TK::ProtectedKeyword, offset) ||
           at(TK::LocalKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    if (at(TK::ConstKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    if (at(TK::VarKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    if (at(TK::StaticKeyword, offset) || at(TK::AutomaticKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    const TK type_start = peek(offset).kind;
    if (type_start == TK::VirtualKeyword &&
        (at(TK::FunctionKeyword, offset + 1) ||
         at(TK::TaskKeyword, offset + 1))) {
      return false;
    }
    const auto after_identifier = type_start == TK::Identifier
                                      ? afterBalancedDimensions(offset + 1)
                                      : std::optional<size_t>{offset + 1};
    if (!after_identifier) {
      return false;
    }
    const size_t boundary = afterOrdinaryDirectives(*after_identifier);
    const bool implicit_type =
        type_start == TK::Identifier &&
        (at(TK::Semicolon, boundary) || at(TK::Equals, boundary) ||
         at(TK::Comma, boundary));
    if (offset == 0 && type_start != TK::Identifier &&
        type_start != TK::VirtualKeyword && type_start != TK::TypeKeyword) {
      return false;
    }
    if (!annexCanStart("data_type_or_implicit", type_start)) {
      return false;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    if (hasAnnexListInterruption(pos_, conditional_members)) {
      static_cast<void>(parseAnnexItem({"class_property"}, true));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    while (at(TK::RandKeyword) || at(TK::RandCKeyword) ||
           at(TK::StaticKeyword) || at(TK::ProtectedKeyword) ||
           at(TK::LocalKeyword)) {
      if (!consumeAnnexRule("property_qualifier", line_)) {
        recordGrammarFallback("invalid Annex A class property qualifier");
        recoverMalformedLeaf(saved);
        return true;
      }
      skip_directives();
    }
    if (at(TK::ConstKeyword)) {
      consumeInto(line_);
      skip_directives();
    }
    if (at(TK::VarKeyword)) {
      consumeInto(line_);
      skip_directives();
    }
    if ((at(TK::StaticKeyword) || at(TK::AutomaticKeyword)) &&
        !consumeAnnexRule("lifetime", line_)) {
      recordGrammarFallback("invalid Annex A class property lifetime");
      recoverMalformedLeaf(saved);
      return true;
    }
    skip_directives();
    if ((!implicit_type && !consumeAnnexRule("data_type_or_implicit", line_)) ||
        !parseVariableAssignmentListRule(conditional_members) ||
        !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A class property declaration");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseClassMethodPrototypeRule() -> bool {
    if (!at(TK::PureKeyword) && !at(TK::ExternKeyword)) {
      return false;
    }
    if (at(TK::ConstraintKeyword, afterOrdinaryDirectives(1))) {
      return false;
    }
    const bool pure = at(TK::PureKeyword);
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        static_cast<void>(parseAnnexItem({"class_method"}, true));
        return true;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // pure / extern
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    bool valid = true;
    if (pure) {
      if (!at(TK::VirtualKeyword)) {
        valid = false;
      } else {
        consumeInto(line_);
      }
      skip_directives();
      while (valid && (at(TK::StaticKeyword) || at(TK::ProtectedKeyword) ||
                       at(TK::LocalKeyword))) {
        valid = consumeAnnexRule("class_item_qualifier", line_);
        skip_directives();
      }
    } else {
      while (valid && (at(TK::VirtualKeyword) || at(TK::StaticKeyword) ||
                       at(TK::ProtectedKeyword) || at(TK::LocalKeyword) ||
                       at(TK::PureKeyword))) {
        valid = consumeAnnexRule("method_qualifier", line_);
        skip_directives();
      }
    }
    if (valid && !pure && at(TK::FunctionKeyword) &&
        at(TK::NewKeyword, afterOrdinaryDirectives(1))) {
      valid = consumeAnnexRule("class_constructor_prototype", line_);
      if (valid && !line_.tokens.empty() &&
          line_.tokens.back().kind == TK::Semicolon) {
        addLine();
        return true;
      }
      valid = false;
    } else if (valid) {
      valid = consumeAnnexRule("method_prototype", line_, TK::Semicolon) &&
              at(TK::Semicolon);
      if (valid) {
        consumeInto(line_);
        addLine();
        return true;
      }
    }
    recordGrammarFallback("invalid Annex A class method prototype");
    recoverMalformedLeaf(saved);
    return true;
  }

  // class_method ::= { method_qualifier } task_declaration |
  //                  { method_qualifier } function_declaration | ... .
  // The declaration keyword selects the child after the qualifier prefix.
  auto parseQualifiedClassMethodRule() -> bool {
    size_t offset = 0;
    while (true) {
      if (at(TK::StaticKeyword, offset) || at(TK::ProtectedKeyword, offset) ||
          at(TK::LocalKeyword, offset) || at(TK::VirtualKeyword, offset)) {
        offset = afterOrdinaryDirectives(offset + 1);
      } else if (at(TK::PureKeyword, offset) &&
                 at(TK::VirtualKeyword, afterOrdinaryDirectives(offset + 1))) {
        const size_t virtual_offset = afterOrdinaryDirectives(offset + 1);
        offset = afterOrdinaryDirectives(virtual_offset + 1);
      } else {
        break;
      }
    }
    if (offset == 0 ||
        (!at(TK::FunctionKeyword, offset) && !at(TK::TaskKeyword, offset))) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    while (at(TK::StaticKeyword) || at(TK::ProtectedKeyword) ||
           at(TK::LocalKeyword) || at(TK::VirtualKeyword) ||
           at(TK::PureKeyword)) {
      if (!consumeAnnexRule("method_qualifier", line_)) {
        recordGrammarFallback("invalid Annex A class method qualifier");
        recoverMalformedItem(saved);
        return true;
      }
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    }
    const TK close =
        at(TK::FunctionKeyword) ? TK::EndFunctionKeyword : TK::EndTaskKeyword;
    if (close != TK::EndFunctionKeyword || !parseClassConstructorRule()) {
      parseNamedBlock(close);
    }
    return true;
  }

  // data_declaration ::= qualified variable declaration |
  // type_declaration | package_import_declaration | nettype_declaration.
  // These children emit their own completed line after class qualifiers.
  auto parseClassPropertyDataChildRule() -> bool {
    if (at(TK::TypedefKeyword)) {
      return parseTypeDeclarationRule();
    }
    if (at(TK::NetTypeKeyword)) {
      return parseNettypeDeclarationRule();
    }
    if (at(TK::ImportKeyword)) {
      return parsePackageImportExportRule();
    }
    if (parseQualifiedDataDeclarationRule() ||
        parseExplicitDataDeclarationRule() || parseUserDataDeclarationRule()) {
      return true;
    }
    return false;
  }

  // class_property ::= { property_qualifier } data_declaration. Once a
  // distinct declaration keyword follows the qualifiers, enter that child
  // rule directly instead of recognizing the entire class_property as a leaf.
  auto parseQualifiedClassDataDeclarationRule() -> bool {
    size_t offset = 0;
    while (at(TK::RandKeyword, offset) || at(TK::RandCKeyword, offset) ||
           at(TK::StaticKeyword, offset) || at(TK::ProtectedKeyword, offset) ||
           at(TK::LocalKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    if (offset == 0 ||
        (!at(TK::TypedefKeyword, offset) && !at(TK::NetTypeKeyword, offset) &&
         !at(TK::ImportKeyword, offset))) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    while (at(TK::RandKeyword) || at(TK::RandCKeyword) ||
           at(TK::StaticKeyword) || at(TK::ProtectedKeyword) ||
           at(TK::LocalKeyword)) {
      if (!consumeAnnexRule("property_qualifier", line_)) {
        recordGrammarFallback("invalid Annex A class property qualifier");
        recoverMalformedItem(saved);
        return true;
      }
      parseGrammarChildDirectiveLines();
    }
    if (parseClassPropertyDataChildRule()) {
      return true;
    }
    recordGrammarFallback("invalid Annex A qualified class declaration");
    recoverMalformedItem(saved);
    return true;
  }

  // The first class_property alternative is a qualifier list followed by
  // data_declaration. Its data child retains local alternatives when a
  // user-defined type makes the declaration prefix ambiguous.
  auto parseQualifiedClassPropertyRule() -> bool {
    if (!at(TK::RandKeyword) && !at(TK::RandCKeyword) &&
        !at(TK::StaticKeyword) && !at(TK::ProtectedKeyword) &&
        !at(TK::LocalKeyword)) {
      return false;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    if (hasAnnexListInterruption(pos_, conditional_members)) {
      static_cast<void>(parseAnnexItem({"class_property"}, true));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = true;
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      valid = consumeAnnexRule("property_qualifier", line_);
      parseGrammarChildDirectiveLines();
    } while (valid && (at(TK::RandKeyword) || at(TK::RandCKeyword) ||
                       at(TK::StaticKeyword) || at(TK::ProtectedKeyword) ||
                       at(TK::LocalKeyword)));
    if (valid && parseClassPropertyDataChildRule()) {
      return true;
    }
    recordGrammarFallback(valid ? "unmatched Annex A class data declaration"
                                : "invalid Annex A class property qualifier");
    recoverMalformedLeaf(saved);
    return true;
  }

  // class_item contains class methods, nested classes, constraints and
  // covergroups. These keyword alternatives call their declaration rules.
  auto parseClassItemRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      // class_item places attributes on exactly these six alternatives.
      if (valid &&
          annexCanStartAny(
              {"class_property", "class_method", "class_constraint",
               "class_declaration", "interface_class_declaration",
               "covergroup_declaration"},
              peek().kind) &&
          parseClassItemRule()) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed class item");
      recoverMalformedItem(saved);
      return true;
    }
    if (at(TK::Semicolon)) {
      consumeInto(line_);
      addLine();
      return true;
    }
    if (parseParameterDeclarationRule()) {
      return true;
    }
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseExplicitDataDeclarationRule() || parseUserDataDeclarationRule()) {
      return true;
    }
    if (parseQualifiedConstClassPropertyRule()) {
      return true;
    }
    if (parseExplicitClassPropertyRule()) {
      return true;
    }
    if (parseClassMethodPrototypeRule()) {
      return true;
    }
    if (parseQualifiedClassMethodRule()) {
      return true;
    }
    if (parseQualifiedClassDataDeclarationRule()) {
      return true;
    }
    if (at(TK::ConstraintKeyword) ||
        (at(TK::StaticKeyword) &&
         at(TK::ConstraintKeyword, afterOrdinaryDirectives(1)))) {
      parseConstraintBlock({"class_constraint"});
      return true;
    }
    if (at(TK::VirtualKeyword) && at(TK::ClassKeyword, 1)) {
      return parsePackageOrGenerateDeclarationRule();
    }
    if (at(TK::RandKeyword) || at(TK::RandCKeyword) || at(TK::ConstKeyword)) {
      if (parseQualifiedClassPropertyRule()) {
        return true;
      }
      static_cast<void>(parseAnnexItem({"class_property"}, true));
      return true;
    }
    if (at(TK::StaticKeyword) || at(TK::ProtectedKeyword) ||
        at(TK::LocalKeyword)) {
      return parseQualifiedClassPropertyRule();
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
    if (parseQualifiedDataDeclarationRule()) {
      return true;
    }
    switch (peek().kind) {
      case TK::FunctionKeyword:
        // checker_or_generate_item_declaration contains function_declaration,
        // but not class_constructor_declaration.
        parseNamedBlock(TK::EndFunctionKeyword);
        return true;
      case TK::CheckerKeyword:
      case TK::CoverGroupKeyword:
      case TK::PropertyKeyword:
      case TK::SequenceKeyword:
        return parsePackageOrGenerateDeclarationRule();
      case TK::ClockingKeyword:
      case TK::GlobalKeyword:
        return parseClockingDeclarationRule();
      default:
        return false;
    }
  }

  // modport_simple_port ::= port_identifier |
  // '.' port_identifier '(' [ expression ] ')'. The named alternative is
  // also the final alternative of ansi_port_declaration after direction.
  [[nodiscard]] auto parseModportSimplePortRule() -> bool {
    parseGrammarChildDirectiveLines();
    const bool named = at(TK::Dot);
    if (named) {
      consumeInto(line_);
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("port_identifier", line_)) {
      return false;
    }
    if (!named) {
      return true;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis) &&
        !consumeAnnexRule("expression", line_, TK::CloseParenthesis)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // modport_tf_port ::= method_prototype | tf_identifier.
  [[nodiscard]] auto parseModportTfPortRule() -> bool {
    parseGrammarChildDirectiveLines();
    return consumeAnnexRule(at(TK::FunctionKeyword) || at(TK::TaskKeyword)
                                ? "method_prototype"
                                : "tf_identifier",
                            line_, TK::Comma);
  }

  auto parseModportPortsDeclarationRule() -> bool {
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      skip_directives();
    }
    const bool simple = at(TK::InputKeyword) || at(TK::OutputKeyword) ||
                        at(TK::InOutKeyword) || at(TK::RefKeyword);
    const bool tf = at(TK::ImportKeyword) || at(TK::ExportKeyword);
    if (simple) {
      if (!consumeAnnexRule("port_direction", line_) ||
          !parseModportSimplePortRule()) {
        return false;
      }
    } else if (tf) {
      if (!consumeAnnexRule("import_export", line_) ||
          !parseModportTfPortRule()) {
        return false;
      }
    } else if (at(TK::ClockingKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      return consumeAnnexRule("clocking_identifier", line_);
    } else {
      return false;
    }
    skip_directives();
    const auto next_port_after_comma = [&] {
      const TK kind = peek(afterOrdinaryDirectives(1)).kind;
      return kind == TK::Identifier || kind == TK::Dot ||
             (tf && (kind == TK::FunctionKeyword || kind == TK::TaskKeyword));
    };
    while (at(TK::Comma) && next_port_after_comma()) {
      consumeInto(line_);
      skip_directives();
      if (!(simple ? parseModportSimplePortRule() : parseModportTfPortRule())) {
        return false;
      }
      skip_directives();
    }
    return true;
  }

  auto parseModportItemRule() -> bool {
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (!consumeAnnexRule("modport_identifier", line_)) {
      return false;
    }
    skip_directives();
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    if (!parseModportPortsDeclarationRule()) {
      return false;
    }
    skip_directives();
    while (at(TK::Comma)) {
      consumeInto(line_);
      if (!parseModportPortsDeclarationRule()) {
        return false;
      }
      skip_directives();
    }
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  auto parseModportDeclarationRule() -> bool {
    if (!at(TK::ModPortKeyword)) {
      return false;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if ((isConditionalStartDirective(token) && !conditional_members) ||
          token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        static_cast<void>(parseAnnexItem({"modport_declaration"}, true));
        return true;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    if (conditional_members) {
      if (!parseConditionalAnnexDeclarationListRule(
              "modport_declaration", [&] { return parseModportItemRule(); })) {
        recordGrammarFallback("invalid Annex A conditional modport items");
        recoverMalformedItem(saved);
      } else {
        addLine();
      }
      return true;
    }
    consumeInto(line_);  // modport
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    bool valid = parseModportItemRule();
    skip_directives();
    while (valid && at(TK::Comma)) {
      consumeInto(line_);
      valid = parseModportItemRule();
      skip_directives();
    }
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A modport item list");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseExternTfDeclarationRule() -> bool {
    const size_t next = afterOrdinaryDirectives(1);
    if (!at(TK::ExternKeyword) ||
        (!at(TK::FunctionKeyword, next) && !at(TK::TaskKeyword, next) &&
         !at(TK::ForkJoinKeyword, next))) {
      return false;
    }
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        static_cast<void>(parseAnnexItem({"extern_tf_declaration"}, true));
        return true;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    consumeInto(line_);  // extern
    skip_directives();
    const bool forkjoin = at(TK::ForkJoinKeyword);
    if (forkjoin) {
      consumeInto(line_);
    }
    skip_directives();
    const bool valid = consumeAnnexRule(
        forkjoin ? "task_prototype" : "method_prototype", line_, TK::Semicolon);
    skip_directives();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A extern task or function");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseInterfaceItemRule(bool allow_port_declaration) -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      // interface_or_generate_item attaches attributes to these children.
      if (valid &&
          annexCanStartAny({"module_common_item", "extern_tf_declaration"},
                           peek().kind) &&
          parseInterfaceItemRule(false)) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed interface item");
      recoverMalformedItem(saved);
      return true;
    }
    if (parseTimeunitsRule()) {
      return true;
    }
    if (parseDefaultClockingOrDisableRule(false)) {
      return true;
    }
    if (allow_port_declaration &&
        (at(TK::InputKeyword) || at(TK::OutputKeyword) ||
         at(TK::InOutKeyword) || at(TK::RefKeyword))) {
      parsePortDeclarationRule();
      return true;
    }
    if (allow_port_declaration &&
        parseQualifiedInterfacePortDeclarationRule()) {
      return true;
    }
    if (at(TK::UnitSystemName) &&
        annexCanStart("checker_instantiation", peek().kind) &&
        parseStructuralInstantiationRule()) {
      return true;
    }
    if (parseParameterDeclarationRule()) {
      return true;
    }
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseExplicitDataDeclarationRule() || parseNetDeclarationRule()) {
      return true;
    }
    if (at(TK::ModPortKeyword)) {
      return parseModportDeclarationRule();
    }
    if (parseExternTfDeclarationRule()) {
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
    if (parseProceduralConstructRule(true)) {
      return true;
    }
    if (parseClockingDeclarationRule()) {
      return true;
    }
    if (parseStructuralInstantiationRule() || parseUserDataDeclarationRule()) {
      return true;
    }
    return parseAssertionItemRule() || parseModuleCommonLeafRule() ||
           parsePackageOrGenerateDeclarationRule() ||
           parseGenerateConstructRule();
  }

  auto parseProgramItemRule(bool allow_port_declaration) -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      // non_port_program_item places attributes on these five alternatives.
      if (valid &&
          annexCanStartAny(
              {"continuous_assign", "module_or_generate_item_declaration",
               "initial_construct", "final_construct",
               "concurrent_assertion_item"},
              peek().kind) &&
          parseProgramItemRule(false)) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed program item");
      recoverMalformedItem(saved);
      return true;
    }
    if (parseTimeunitsRule()) {
      return true;
    }
    if (parseDefaultClockingOrDisableRule(false)) {
      return true;
    }
    if (allow_port_declaration &&
        (at(TK::InputKeyword) || at(TK::OutputKeyword) ||
         at(TK::InOutKeyword) || at(TK::RefKeyword))) {
      parsePortDeclarationRule();
      return true;
    }
    if (allow_port_declaration &&
        parseQualifiedInterfacePortDeclarationRule()) {
      return true;
    }
    if (parseParameterDeclarationRule()) {
      return true;
    }
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseExplicitDataDeclarationRule() || parseNetDeclarationRule() ||
        parseUserDataDeclarationRule()) {
      return true;
    }
    if (at(TK::GenerateKeyword)) {
      parseSimpleBlock(TK::EndGenerateKeyword);
      return true;
    }
    if (parseProceduralConstructRule(false)) {
      return true;
    }
    if (parseClockingDeclarationRule()) {
      return true;
    }
    return parseConcurrentAssertionRule() || parseModuleCommonLeafRule(true) ||
           parsePackageOrGenerateDeclarationRule() ||
           parseGenerateConstructRule();
  }

  // generate_item ::= module_or_generate_item |
  // interface_or_generate_item | checker_or_generate_item.
  auto parseRandCheckerDataDeclarationRule() -> bool {
    if (!at(TK::RandKeyword)) {
      return false;
    }
    const auto after_implicit =
        at(TK::Identifier, 1) ? afterBalancedDimensions(2) : std::nullopt;
    const bool implicit_identifier =
        after_implicit &&
        (at(TK::Semicolon, *after_implicit) ||
         at(TK::Equals, *after_implicit) || at(TK::Comma, *after_implicit));
    const size_t type_offset =
        at(TK::UnitSystemName, 1) && at(TK::DoubleColon, 2) ? 3 : 1;
    const auto after_type = afterUserTypePrefix(type_offset);
    if (implicit_identifier ||
        (after_type && at(TK::Identifier, *after_type))) {
      const LeafCheckpoint saved = leafCheckpoint();
      const bool conditional_members = hasConditionalListMember(pos_);
      const bool interrupted =
          hasAnnexListInterruption(pos_, conditional_members);
      consumeInto(line_);  // rand
      bool valid = implicit_identifier ||
                   consumeAnnexRule("data_type_or_implicit", line_);
      if (valid) {
        valid = interrupted
                    ? consumeAnnexRule("list_of_variable_decl_assignments",
                                       line_, TK::Semicolon)
                    : parseVariableAssignmentListRule(conditional_members);
      }
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A rand data declaration");
        recoverMalformedLeaf(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // rand
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseQualifiedDataDeclarationRule() ||
        parseExplicitDataDeclarationRule() ||
        (at(TK::ImportKeyword) && parsePackageImportExportRule()) ||
        parseUserDataDeclarationRule()) {
      return true;
    }
    // The only checker declaration with a leading rand is [rand]
    // data_declaration. Keep the ambiguous data child local to that rule.
    if (!consumeAnnexRule("data_declaration", line_) || line_.tokens.empty() ||
        line_.tokens.back().kind != TK::Semicolon) {
      recordGrammarFallback("invalid Annex A rand data declaration");
      recoverMalformedItem(saved);
      return true;
    }
    addLine();
    return true;
  }

  auto parseGenerateItemRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      // generate_item reaches attributes through these two productions.
      if (valid &&
          annexCanStartAny(
              {"module_or_generate_item", "interface_or_generate_item"},
              peek().kind) &&
          parseGenerateItemRule()) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed generate item");
      recoverMalformedItem(saved);
      return true;
    }
    if (parseDefaultClockingOrDisableRule(false)) {
      return true;
    }
    if (at(TK::UnitSystemName) &&
        annexCanStart("checker_instantiation", peek().kind) &&
        parseStructuralInstantiationRule()) {
      return true;
    }
    if (parseRandCheckerDataDeclarationRule()) {
      return true;
    }
    if (parseParameterDeclarationRule()) {
      return true;
    }
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseExplicitDataDeclarationRule() || parseNetDeclarationRule() ||
        parseParameterOverrideRule()) {
      return true;
    }
    if (at(TK::GenerateKeyword)) {
      parseSimpleBlock(TK::EndGenerateKeyword);
      return true;
    }
    if (parseProceduralConstructRule(true)) {
      return true;
    }
    if (parseClockingDeclarationRule()) {
      return true;
    }
    if (parseGateInstantiationRule() || parseUdpInstantiationRule() ||
        parseStructuralInstantiationRule() || parseUserDataDeclarationRule()) {
      return true;
    }
    return parseAssertionItemRule() || parseModuleCommonLeafRule() ||
           parsePackageOrGenerateDeclarationRule() ||
           parseGenerateConstructRule();
  }

  auto parseCheckerItemRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      // checker_declaration repeats { attribute_instance }
      // checker_or_generate_item, although the child has no attributes.
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      if (valid && parseCheckerItemRule()) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed checker item");
      recoverMalformedItem(saved);
      return true;
    }
    if (at(TK::Semicolon)) {
      consumeInto(line_);
      addLine();
      return true;
    }
    if (parseDefaultClockingOrDisableRule(true)) {
      return true;
    }
    if (parseRandCheckerDataDeclarationRule()) {
      return true;
    }
    if (parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
        parseExplicitDataDeclarationRule() || parseUserDataDeclarationRule()) {
      return true;
    }
    return parseAssertionItemRule() || parseModuleCommonLeafRule(true) ||
           parseCheckerDeclarationRule() || parseGenerateConstructRule() ||
           parseProceduralConstructRule(true);
  }

  auto parsePackageItemRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      // package_declaration repeats { attribute_instance } package_item.
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      if (valid && parsePackageItemRule()) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed package item");
      recoverMalformedItem(saved);
      return true;
    }
    if (parseTimeunitsRule()) {
      return true;
    }
    if (parseAnonymousProgramRule()) {
      return true;
    }
    if (at(TK::ExportKeyword)) {
      if (parseDpiDeclarationRule()) {
        return true;
      }
      return parsePackageImportExportRule();
    }
    return parseParameterDeclarationRule() || parseTypeDeclarationRule() ||
           parseNettypeDeclarationRule() ||
           parseExplicitDataDeclarationRule() || parseNetDeclarationRule() ||
           parseUserDataDeclarationRule() ||
           parsePackageOrGenerateDeclarationRule();
  }

  // interface_class_item ::= type_declaration |
  // { attribute_instance } interface_class_method |
  // local_parameter_declaration ';' | parameter_declaration ';' | ';'.
  auto parseInterfaceClassItemRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      if (valid && annexCanStart("interface_class_method", peek().kind) &&
          parseInterfaceClassItemRule()) {
        return true;
      }
      recordGrammarFallback(
          "invalid Annex A attributed interface class method");
      recoverMalformedItem(saved);
      return true;
    }
    if (at(TK::Semicolon)) {
      consumeInto(line_);
      addLine();
      return true;
    }
    if (parseParameterDeclarationRule() || parseTypeDeclarationRule()) {
      return true;
    }
    if (at(TK::PureKeyword) && at(TK::VirtualKeyword, 1)) {
      for (size_t i = pos_; i < tokens_.size(); ++i) {
        const auto& token = tokens_[i];
        if (isConditionalStartDirective(token) ||
            token.kind == TK::MacroUsage ||
            (token.kind == TK::Directive && !isCompilerDirective(token))) {
          static_cast<void>(parseAnnexItem({"interface_class_method"}, true));
          return true;
        }
        if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
          break;
        }
      }
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);  // pure
      consumeInto(line_);  // virtual
      if (!consumeAnnexRule("method_prototype", line_, TK::Semicolon) ||
          !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A interface class method");
        recoverMalformedLeaf(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    return false;
  }

  // anonymous_program ::= 'program' ';' { anonymous_program_item }
  // 'endprogram'. Its header terminals are consumed here; body items call
  // their productions through parseDelimitedBody().
  auto parseAnonymousProgramRule() -> bool {
    if (!at(TK::ProgramKeyword) || !at(TK::Semicolon, 1)) {
      return false;
    }
    consumeInto(line_);
    consumeInto(line_);
    addLine();
    parseDelimitedBody(TK::EndProgramKeyword, "anonymous_program_item");
    return true;
  }

  auto parseAnonymousProgramItemRule() -> bool {
    switch (peek().kind) {
      case TK::Semicolon:
        consumeInto(line_);
        addLine();
        return true;
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

  auto parseTfVariableIdentifierListRule(bool conditional_members) -> bool {
    return parsePortIdentifierDimensionListRule(
        "list_of_tf_variable_identifiers", "port_identifier",
        "variable_dimension", "expression", conditional_members);
  }

  // These Annex A lists repeat an unnamed identifier and dimension
  // sequence. Keep the parent live across complete conditional members,
  // while ordinary members enter their Annex A child rules directly.
  auto parsePortIdentifierWithDimensionsRule(
      std::string_view  // NOLINT(bugprone-easily-swappable-parameters)
          identifier,
      std::string_view dimension, std::string_view initializer) -> bool {
    if (!consumeAnnexRule(identifier, line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule(dimension, line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (!initializer.empty() && at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule(initializer, line_, TK::Comma)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    return true;
  }

  auto parsePortIdentifierDimensionListRule(
      std::string_view list,  // NOLINT(bugprone-easily-swappable-parameters)
      std::string_view identifier, std::string_view dimension,
      std::string_view initializer, bool conditional_members) -> bool {
    if (!conditional_members) {
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        parseGrammarChildDirectiveLines();
        if (!parsePortIdentifierWithDimensionsRule(identifier, dimension,
                                                   initializer)) {
          return false;
        }
        parseGrammarChildDirectiveLines();
        if (!at(TK::Comma)) {
          break;
        }
        consumeInto(line_);
      } while (!at(TK::EndOfFile));
      return true;
    }
    beginGrammar({list});
    bool valid = true;
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      if (grammar_scopes_.back().complete() && at(TK::Semicolon)) {
        break;
      }
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        valid =
            parseAnnexConditional(TK::EndOfFile, header_ended, indent_level_);
      } else if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      } else if (at(TK::Comma)) {
        valid = grammarAllows(TK::Comma);
        if (valid) {
          consumeInto(line_);
        }
      } else {
        valid = grammarAllows(peek().kind) &&
                parsePortIdentifierWithDimensionsRule(identifier, dimension,
                                                      initializer);
      }
      if (!valid || grammar_scopes_.back().failed ||
          grammar_scopes_.back().interrupted) {
        break;
      }
    }
    const AnnexState result = endGrammar(false);
    return valid && !result.failed && !result.interrupted &&
           result.complete() && at(TK::Semicolon);
  }

  auto parseTfPortDeclarationRule() -> bool {
    size_t attributes = 0;
    while (at(TK::OpenParenthesis, attributes) &&
           at(TK::Star, attributes + 1)) {
      const auto after = afterBalancedParentheses(attributes);
      if (!after || !at(TK::Star, *after - 2)) {
        return false;
      }
      attributes = *after;
    }
    const bool direction =
        annexCanStart("tf_port_direction", peek(attributes).kind) &&
        (!at(TK::ConstKeyword, attributes) ||
         at(TK::RefKeyword, afterOrdinaryDirectives(attributes + 1)));
    if (!direction) {
      return false;
    }
    const bool ref_direction =
        at(TK::RefKeyword, attributes) || at(TK::ConstKeyword, attributes);
    size_t offset = afterOrdinaryDirectives(attributes + 1);
    if (at(TK::ConstKeyword, attributes)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    if (at(TK::StaticKeyword, offset) && ref_direction) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    if (at(TK::VarKeyword, offset)) {
      offset = afterOrdinaryDirectives(offset + 1);
    }
    const TK type_start = peek(offset).kind;
    bool dimensioned_implicit = false;
    if (type_start == TK::Identifier && at(TK::OpenBracket, offset + 1)) {
      const auto next = afterBalancedDimensions(offset + 1);
      if (!next) {
        static_cast<void>(parseAnnexItem({"tf_port_declaration"}, true));
        return true;
      }
      const size_t boundary = afterOrdinaryDirectives(*next);
      dimensioned_implicit = at(TK::Semicolon, boundary) ||
                             at(TK::Equals, boundary) ||
                             at(TK::Comma, boundary);
      if (!dimensioned_implicit && !at(TK::Identifier, boundary)) {
        static_cast<void>(parseAnnexItem({"tf_port_declaration"}, true));
        return true;
      }
    }
    const size_t after_type_start = afterOrdinaryDirectives(offset + 1);
    const bool implicit_type =
        dimensioned_implicit ||
        (type_start == TK::Identifier &&
         (at(TK::Semicolon, after_type_start) ||
          at(TK::Equals, after_type_start) || at(TK::Comma, after_type_start)));
    if (!annexCanStart("data_type_or_implicit", type_start)) {
      static_cast<void>(parseAnnexItem({"tf_port_declaration"}, true));
      return true;
    }
    const bool conditional_members = hasConditionalListMember(pos_);
    if (hasAnnexListInterruption(pos_, conditional_members)) {
      static_cast<void>(parseAnnexItem({"tf_port_declaration"}, true));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = true;
    while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      valid = consumeAnnexRule("attribute_instance", line_);
      parseGrammarChildDirectiveLines();
    }
    if (valid) {
      valid = parseTfPortDirectionRule();
    }
    parseGrammarChildDirectiveLines();
    if (valid && at(TK::VarKeyword)) {
      consumeInto(line_);
    }
    parseGrammarChildDirectiveLines();
    if (valid && !implicit_type) {
      valid = consumeAnnexRule("data_type_or_implicit", line_);
    }
    parseGrammarChildDirectiveLines();
    if (valid) {
      valid = parseTfVariableIdentifierListRule(conditional_members);
    }
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A task or function port");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseBlockOrTfItemDeclarationRule(bool allow_tf_port) -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      // Both block_item_declaration and tf_port_declaration start with a
      // sequence of attribute_instance children. Keep them on the current
      // line, then enter the selected declaration child directly.
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      if (valid && parseBlockOrTfItemDeclarationRule(allow_tf_port)) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed block item");
      recoverMalformedItem(saved);
      return true;
    }
    if (parseParameterDeclarationRule()) {
      return true;
    }
    if (parseQualifiedDataDeclarationRule()) {
      return true;
    }
    if (at(TK::ImportKeyword)) {
      if (parsePackageImportExportRule()) {
        return true;
      }
      static_cast<void>(parseAnnexItem({"data_declaration"}, true));
      return true;
    }
    if (at(TK::LetKeyword)) {
      return parseLetDeclarationRule();
    }
    if (allow_tf_port && parseTfPortDeclarationRule()) {
      return true;
    }
    return parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
           parseExplicitDataDeclarationRule() || parseUserDataDeclarationRule();
  }

  auto parseProceduralConstructRule(bool allow_always) -> bool {
    const TK kind = peek().kind;
    if (kind != TK::InitialKeyword && kind != TK::FinalKeyword &&
        !(allow_always &&
          (kind == TK::AlwaysKeyword || kind == TK::AlwaysCombKeyword ||
           kind == TK::AlwaysFFKeyword || kind == TK::AlwaysLatchKeyword))) {
      return false;
    }
    parseProceduralBlock();
    return true;
  }

  // list_of_net_assignments and list_of_variable_assignments both consist of
  // comma-separated assignment children. Keep the alternatives that complete
  // each child, so a list cannot switch production halfway through.
  [[nodiscard]] auto parseContinuousAssignmentListRule(
      bool net_possible, bool variable_possible,
      bool conditional_members = false) -> bool {
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek()) &&
             (!conditional_members || !isConditionalStartDirective(peek()))) {
        addLine();
        parseDirectiveLine();
      }
    };
    while (!at(TK::EndOfFile)) {
      skip_directives();
      if (conditional_members && isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_)) {
          return false;
        }
        continue;
      }
      if (!net_possible && !variable_possible) {
        return false;
      }
      if (net_possible && variable_possible) {
        const AnnexState assignment = parseAnnexItem(
            {"net_assignment", "variable_assignment"}, false, true);
        if (assignment.failed || assignment.interrupted ||
            !assignment.complete()) {
          return false;
        }
        net_possible = assignment.completed("net_assignment");
        variable_possible = assignment.completed("variable_assignment");
      } else if (!consumeAnnexRule(
                     net_possible ? "net_assignment" : "variable_assignment",
                     line_, TK::Comma)) {
        return false;
      }
      if (!net_possible && !variable_possible) {
        return false;
      }
      skip_directives();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    }
    return net_possible || variable_possible;
  }

  auto parseConditionalContinuousAssignmentRule() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"continuous_assign"});
    bool valid = grammarAllows(TK::AssignKeyword);
    if (valid) {
      consumeInto(line_);
    }
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    bool net_possible = true;
    bool variable_possible = true;
    if (valid && at(TK::OpenParenthesis)) {
      valid = consumeAnnexRule("drive_strength", line_);
      skip_directives();
      if (valid && at(TK::Hash)) {
        valid = consumeAnnexRule("delay3", line_);
      }
      variable_possible = false;
    } else if (valid && at(TK::Hash)) {
      const AnnexState delay =
          parseAnnexItem({"delay3", "delay_control"}, false, true);
      valid = !delay.failed && !delay.interrupted && delay.complete();
      net_possible = delay.completed("delay3");
      variable_possible = delay.completed("delay_control");
    }
    if (valid) {
      valid = parseContinuousAssignmentListRule(net_possible, variable_possible,
                                                true);
    }
    if (valid && at(TK::Semicolon) && grammarAllows(TK::Semicolon)) {
      consumeInto(line_);
    } else {
      valid = false;
    }
    const AnnexState result = endGrammar(false);
    if (!valid || result.failed || result.interrupted || !result.complete()) {
      recordGrammarFallback("invalid Annex A conditional assignment list");
      recoverMalformedItem(saved);
      return;
    }
    addLine();
  }

  // list_of_genvar_identifiers ::= genvar_identifier
  // { ',' genvar_identifier }.
  [[nodiscard]] auto parseGenvarIdentifierListRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("genvar_identifier", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // module_common_item has distinct leading terminals for these leaf
  // productions. Program and checker items include continuous_assign and
  // elaboration_severity_system_task, but not net_alias or bind_directive.
  auto parseModuleCommonLeafRule(bool continuous_only = false) -> bool {
    if (at(TK::SystemIdentifier)) {
      const std::string_view name = peek().rawText();
      if (name == "$fatal" || name == "$error" || name == "$warning" ||
          name == "$info") {
        const LeafCheckpoint saved = leafCheckpoint();
        if (!consumeAnnexRule("severity_system_task", line_) ||
            line_.tokens.empty() || line_.tokens.back().kind != TK::Semicolon) {
          recordGrammarFallback("invalid Annex A elaboration severity task");
          recoverMalformedLeaf(saved);
        } else {
          addLine();
        }
        return true;
      }
    }
    if (at(TK::GenVarKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      const bool conditional_members = hasConditionalListMember(pos_);
      const bool interrupted =
          hasAnnexListInterruption(pos_, conditional_members);
      consumeInto(line_);
      if (!(interrupted ? consumeAnnexRule("list_of_genvar_identifiers", line_,
                                           TK::Semicolon)
            : conditional_members
                ? parseConditionalAnnexCommaListRule(
                      "list_of_genvar_identifiers", "genvar_identifier")
                : parseGenvarIdentifierListRule()) ||
          !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A genvar declaration");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    if (at(TK::AssignKeyword)) {
      const bool conditional_members = hasConditionalListMember(pos_);
      if (hasAnnexListInterruption(pos_, conditional_members)) {
        static_cast<void>(parseAnnexItem({"continuous_assign"}, true));
        return true;
      }
      if (conditional_members) {
        parseConditionalContinuousAssignmentRule();
        return true;
      }
      const size_t item_start = afterOrdinaryDirectives(1);
      const auto skip_directives = [&] {
        while (afterOrdinaryDirectives(0) > 0) {
          addLine();
          parseDirectiveLine();
        }
      };
      if (at(TK::Hash, item_start)) {
        const LeafCheckpoint saved = leafCheckpoint();
        consumeInto(line_);  // assign
        skip_directives();
        const AnnexState delay =
            parseAnnexItem({"delay3", "delay_control"}, false, true);
        if (delay.failed || delay.interrupted || !delay.complete()) {
          recordGrammarFallback("invalid Annex A continuous assign delay");
          recoverMalformedLeaf(saved);
          return true;
        }
        const bool net_possible = delay.completed("delay3");
        const bool variable_possible = delay.completed("delay_control");
        if (!net_possible && !variable_possible) {
          recordGrammarFallback("unresolved Annex A continuous assign delay");
          recoverMalformedLeaf(saved);
          return true;
        }
        if (!parseContinuousAssignmentListRule(net_possible,
                                               variable_possible) ||
            !at(TK::Semicolon)) {
          recordGrammarFallback("invalid Annex A delayed assignment");
          recoverMalformedLeaf(saved);
          return true;
        }
        consumeInto(line_);
        addLine();
        return true;
      }
      if (at(TK::OpenParenthesis, item_start)) {
        const LeafCheckpoint saved = leafCheckpoint();
        consumeInto(line_);  // assign
        skip_directives();
        bool valid = consumeAnnexRule("drive_strength", line_);
        skip_directives();
        if (valid && at(TK::Hash)) {
          valid = consumeAnnexRule("delay3", line_);
        }
        if (valid) {
          valid = parseContinuousAssignmentListRule(true, false);
        }
        if (!valid || !at(TK::Semicolon)) {
          recordGrammarFallback("invalid Annex A driven assignment");
          recoverMalformedLeaf(saved);
          return true;
        }
        consumeInto(line_);
        addLine();
        return true;
      }
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);  // assign
      if (!parseContinuousAssignmentListRule(true, true) ||
          !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A continuous assignment");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    if (!continuous_only && at(TK::AliasKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);
      if (!consumeAnnexRule("net_lvalue", line_, TK::Equals) ||
          !at(TK::Equals)) {
        recordGrammarFallback("invalid Annex A net alias source");
        recoverMalformedItem(saved);
        return true;
      }
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        consumeInto(line_);
        if (!consumeAnnexRule("net_lvalue", line_, TK::Equals)) {
          recordGrammarFallback("invalid Annex A net alias destination");
          recoverMalformedItem(saved);
          return true;
        }
      } while (at(TK::Equals));
      if (!at(TK::Semicolon)) {
        recordGrammarFallback("missing Annex A net alias semicolon");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    if (!continuous_only && at(TK::BindKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      for (size_t i = pos_; i < tokens_.size(); ++i) {
        const auto& token = tokens_[i];
        if (isConditionalStartDirective(token) ||
            token.kind == TK::MacroUsage ||
            (token.kind == TK::Directive && !isCompilerDirective(token))) {
          const AnnexState item = parseAnnexItem({"bind_directive"}, true);
          if (item.failed || item.interrupted || !item.complete()) {
            recoverMalformedItem(saved);
          }
          return true;
        }
        if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
          break;
        }
      }
      consumeInto(line_);  // bind
      const AnnexState target = parseAnnexItem(
          {"bind_target_scope", "bind_target_instance"}, false, true);
      if (target.interrupted) {
        return true;
      }
      const bool scope_target = target.completed("bind_target_scope");
      bool valid = !target.failed && target.complete() &&
                   (scope_target || target.completed("bind_target_instance"));
      if (valid && at(TK::Colon)) {
        if (!scope_target) {
          valid = false;
        } else {
          consumeInto(line_);
          parseGrammarChildDirectiveLines();
          valid = consumeAnnexRule("bind_target_instance_list", line_);
        }
      }
      if (valid) {
        bool instantiation_valid = false;
        const bool recognized =
            parseStructuralInstantiationRule(false, &instantiation_valid);
        if (recognized && !instantiation_valid) {
          return true;
        }
        valid = recognized && instantiation_valid;
      }
      // Annex A appends a semicolon to bind_instantiation, whose own
      // alternatives already include one. Preserve that literal production.
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A bind directive");
        recoverMalformedLeaf(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    return false;
  }

  // procedural_continuous_assignment ::= 'assign' variable_assignment
  // | 'deassign' variable_lvalue | 'force' (variable_assignment |
  // net_assignment) | 'release' (variable_lvalue | net_lvalue).
  // The force/release children retain their Annex A ambiguity locally.
  auto parseProceduralContinuousAssignmentRule() -> bool {
    const TK keyword = peek().kind;
    if (keyword != TK::AssignKeyword && keyword != TK::DeassignKeyword &&
        keyword != TK::ForceKeyword && keyword != TK::ReleaseKeyword) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    bool valid = false;
    if (keyword == TK::AssignKeyword || keyword == TK::DeassignKeyword) {
      valid =
          consumeAnnexRule(keyword == TK::AssignKeyword ? "variable_assignment"
                                                        : "variable_lvalue",
                           line_, TK::Semicolon);
    } else {
      const AnnexState child = parseAnnexItem(
          keyword == TK::ForceKeyword
              ? std::vector<std::string_view>{"variable_assignment",
                                              "net_assignment"}
              : std::vector<std::string_view>{"variable_lvalue", "net_lvalue"},
          false, true);
      if (child.interrupted) {
        return true;
      }
      valid = !child.failed && child.complete();
    }
    parseGrammarChildDirectiveLines();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A procedural continuous assignment");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // statement_item ::= ... | case_statement | conditional_statement |
  // loop_statement | par_block | seq_block | randcase_statement | ... .
  // These alternatives have distinct leading terminals. Leaf alternatives
  // continue through their local Annex A rule below.
  auto parseStatementItemRule() -> bool {
    switch (peek().kind) {
      case TK::AssignKeyword:
      case TK::DeassignKeyword:
      case TK::ForceKeyword:
      case TK::ReleaseKeyword:
        return parseProceduralContinuousAssignmentRule();
      case TK::ReturnKeyword:
      case TK::BreakKeyword:
      case TK::ContinueKeyword:
        return parseJumpStatementRule();
      case TK::DisableKeyword:
        return parseDisableStatementRule();
      case TK::MinusArrow:
      case TK::MinusDoubleArrow:
        return parseEventTriggerRule();
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

  // statement_item alternatives for calls and assignments share tokens until
  // the call, assignment, or clocking drive is complete.
  // Keep only those Annex A children live while emitting the statement.
  auto parseAssignmentOrCallStatementRule() -> bool {
    if (!at(TK::Identifier) && !at(TK::UnitSystemName) &&
        !at(TK::RootSystemName) && !at(TK::ThisKeyword) &&
        !at(TK::SuperKeyword) && !at(TK::OpenBrace) &&
        !at(TK::ApostropheOpenBrace) && !at(TK::DoublePlus) &&
        !at(TK::DoubleMinus)) {
      return false;
    }
    bool interrupted = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        interrupted = true;
        break;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const auto blocking_operator = [](TK kind) {
      return annexCanStart("assignment_operator", kind) ||
             annexCanStart("inc_or_dec_operator", kind);
    };
    bool blocking =
        !interrupted && (annexCanStart("inc_or_dec_operator", peek().kind) ||
                         blocking_operator(peek(1).kind));
    bool nonblocking = !interrupted && at(TK::LessThanEquals, 1);
    size_t assignment_offset = nonblocking ? 1 : 0;
    if (!interrupted && !blocking && !nonblocking &&
        (at(TK::OpenBracket, 1) || at(TK::Dot, 1) || at(TK::DoubleColon, 1) ||
         at(TK::OpenBrace) || at(TK::ApostropheOpenBrace))) {
      ListDepth depth;
      if (at(TK::OpenBrace) || at(TK::ApostropheOpenBrace)) {
        advanceListDepth(depth, peek().kind);
      }
      for (size_t i = pos_ + 1; i < tokens_.size(); ++i) {
        const TK kind = tokens_[i].kind;
        if (depth.topLevel() && kind == TK::LessThanEquals) {
          nonblocking = true;
          assignment_offset = i - pos_;
          break;
        }
        if (depth.topLevel() && blocking_operator(kind)) {
          blocking = true;
          break;
        }
        if (depth.topLevel() &&
            (kind == TK::Semicolon || kind == TK::EndOfFile)) {
          break;
        }
        if (depth.topLevel() &&
            std::ranges::any_of(block_stack_, [kind](const BlockFrame& frame) {
              return matchesBlockClose(frame.close_kind, kind);
            })) {
          break;
        }
        advanceListDepth(depth, kind);
      }
    }
    if (nonblocking) {
      const LeafCheckpoint saved = leafCheckpoint();
      const std::string_view rule = at(TK::DoubleHash, assignment_offset + 1)
                                        ? "clocking_drive"
                                        : "nonblocking_assignment";
      if (!consumeAnnexRule(rule, line_, TK::Semicolon) || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A nonblocking statement");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    if (blocking) {
      const LeafCheckpoint saved = leafCheckpoint();
      if (!consumeAnnexRule("blocking_assignment", line_, TK::Semicolon) ||
          !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A blocking assignment");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    if (!interrupted) {
      if (!consumeAnnexRule("subroutine_call", line_, TK::Semicolon) ||
          !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A subroutine call statement");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    const AnnexState item =
        parseAnnexItem({"blocking_assignment", "nonblocking_assignment",
                        "subroutine_call_statement", "clocking_drive"},
                       false, true);
    if (item.interrupted) {
      return true;
    }
    if (item.failed || !item.complete()) {
      recordGrammarFallback("invalid Annex A identifier statement");
      recoverMalformedItem(saved);
      return true;
    }
    if (at(TK::Semicolon)) {
      consumeInto(line_);
    }
    if (line_.tokens.empty() || line_.tokens.back().kind != TK::Semicolon) {
      recordGrammarFallback("missing Annex A statement semicolon");
      recoverMalformedItem(saved);
      return true;
    }
    addLine();
    return true;
  }

  auto parseJumpStatementRule() -> bool {
    if (!at(TK::ReturnKeyword) && !at(TK::BreakKeyword) &&
        !at(TK::ContinueKeyword)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const bool returns = at(TK::ReturnKeyword);
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (returns && !at(TK::Semicolon) &&
        !consumeAnnexRule("expression", line_, TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A return expression");
      recoverMalformedItem(saved);
      return true;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A jump semicolon");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseDisableStatementRule() -> bool {
    if (!at(TK::DisableKeyword)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (at(TK::ForkKeyword)) {
      consumeInto(line_);
    } else if (!consumeAnnexRule("hierarchical_task_identifier", line_)) {
      recordGrammarFallback("invalid Annex A disable target");
      recoverMalformedItem(saved);
      return true;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A disable semicolon");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseEventTriggerRule() -> bool {
    if (!at(TK::MinusArrow) && !at(TK::MinusDoubleArrow)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const bool delayed = at(TK::MinusDoubleArrow);
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (delayed && (at(TK::Hash) || at(TK::At) || at(TK::RepeatKeyword)) &&
        !consumeAnnexRule("delay_or_event_control", line_)) {
      recordGrammarFallback("invalid Annex A delayed event trigger");
      recoverMalformedItem(saved);
      return true;
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("hierarchical_event_identifier", line_)) {
      recordGrammarFallback("invalid Annex A event trigger target");
      recoverMalformedItem(saved);
      return true;
    }
    parseGrammarChildDirectiveLines();
    if ((at(TK::Dot) || at(TK::OpenBracket)) &&
        !consumeAnnexRule("nonrange_select", line_)) {
      recordGrammarFallback("invalid Annex A event trigger select");
      recoverMalformedItem(saved);
      return true;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A event trigger semicolon");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // procedural_timing_control_statement ::= procedural_timing_control
  // statement_or_null. The control is one Annex A child; the body calls the
  // statement production while output lines are emitted from this pass.
  auto parseProceduralTimingControlStatementRule(bool join_loop_begin = false)
      -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    const bool control = consumeAnnexRule("procedural_timing_control", line_);
    if (!control) {
      recordGrammarFallback("invalid Annex A procedural timing control");
      recoverMalformedItem(saved);
      return;
    }
    if (join_loop_begin) {
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek()) &&
             !isConditionalBoundaryDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
      if (atEnclosingBoundary()) {
        recordGrammarFallback("missing Annex A procedural timing body");
        recoverMalformedItem(saved);
        return;
      }
      if (at(TK::BeginKeyword)) {
        parseBeginEnd(TK::EndKeyword);
      } else {
        addLine();
        parseIndentedStatement({"statement_or_null"});
      }
      return;
    }
    parseGrammarChildDirectiveLines();
    const bool compound =
        at(TK::BeginKeyword) || at(TK::ForkKeyword) || at(TK::IfKeyword) ||
        at(TK::CaseKeyword) || at(TK::CaseXKeyword) || at(TK::CaseZKeyword) ||
        at(TK::ForKeyword) || at(TK::ForeachKeyword) || at(TK::WhileKeyword) ||
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
  auto parseConditionalWaitStatementRule() -> bool {
    if (at(TK::WaitOrderKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      beginGrammar({"wait_statement"});
      while (!at(TK::EndOfFile) &&
             !grammar_scopes_.back().hasActiveRule("action_block")) {
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
        if (!grammar_scopes_.back().accepts(peek().kind)) {
          break;
        }
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
    if (!at(TK::WaitKeyword)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"wait_statement"});
    consumeInto(line_);  // wait
    while (isCompilerDirective(peek())) {
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_)) {
          static_cast<void>(endGrammar(false));
          recoverMalformedItem(saved);
          return true;
        }
      } else {
        addLine();
        parseDirectiveLine();
      }
    }
    if (!at(TK::OpenParenthesis)) {
      if (at(TK::ForkKeyword) && grammarAllows(TK::ForkKeyword)) {
        consumeInto(line_);
        const bool valid = at(TK::Semicolon) && grammarAllows(TK::Semicolon);
        if (valid) {
          consumeInto(line_);
        }
        const AnnexState wait = endGrammar(false);
        if (!valid || wait.failed || wait.interrupted || !wait.complete()) {
          recordGrammarFallback("invalid Annex A conditional wait fork");
          recoverMalformedItem(saved);
        } else {
          addLine();
        }
        return true;
      }
      parseGrammarLeaf(true, saved);
      static_cast<void>(endGrammar());
      return true;
    }
    const bool condition = consumeAnnexDelimited(
        TK::OpenParenthesis, TK::CloseParenthesis, "expression", line_);
    const AnnexState prefix = endGrammar(false);
    if (!condition || prefix.failed || prefix.interrupted ||
        !prefix.hasActiveRule("statement_or_null") || line_.tokens.empty() ||
        line_.tokens.back().kind != TK::CloseParenthesis) {
      recordGrammarFallback("invalid Annex A wait condition");
      recoverMalformedItem(saved);
      return true;
    }
    addLine();
    parseIndentedStatement({"statement_or_null"});
    return true;
  }

  auto parseWaitStatementRule() -> bool {
    if (!at(TK::WaitKeyword) && !at(TK::WaitOrderKeyword)) {
      return false;
    }
    // A conditional directive can select a different production in the
    // header. Keep the interrupted grammar scope for that case.
    if (isConditionalStartDirective(peek(1))) {
      return parseConditionalWaitStatementRule();
    }

    const LeafCheckpoint saved = leafCheckpoint();
    const bool ordered = at(TK::WaitOrderKeyword);
    consumeInto(line_);
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek()) &&
           !isConditionalBoundaryDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if (!ordered && at(TK::ForkKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (at(TK::Semicolon)) {
        consumeInto(line_);
        addLine();
      } else {
        recordGrammarFallback("invalid Annex A wait fork statement");
        recoverMalformedItem(saved);
      }
      return true;
    }
    if (!at(TK::OpenParenthesis)) {
      recordGrammarFallback("invalid Annex A wait header");
      recoverMalformedItem(saved);
      return true;
    }
    if (ordered) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      bool valid =
          consumeAnnexRule("hierarchical_identifier", line_, TK::Comma);
      parseGrammarChildDirectiveLines();
      while (valid && at(TK::Comma)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
        valid = consumeAnnexRule("hierarchical_identifier", line_, TK::Comma);
        parseGrammarChildDirectiveLines();
      }
      if (!valid || !at(TK::CloseParenthesis)) {
        recordGrammarFallback("invalid Annex A wait_order identifier list");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      parseActionBlockRule();
      return true;
    }
    const bool condition = consumeAnnexDelimited(
        TK::OpenParenthesis, TK::CloseParenthesis, "expression", line_);
    if (!condition && !unavailableMacroIn(saved.pos, pos_)) {
      recoverMalformedItem(saved);
      return true;
    }
    if (line_.tokens.empty() ||
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
  auto parseStatementLabelRule(const std::vector<std::string_view>& roots)
      -> bool {
    if (!at(TK::Identifier) || !at(TK::Colon, 1)) {
      return false;
    }
    AnnexState label(roots);
    label.advance(peek());
    label.advance(peek(1));
    if (label.failed) {
      return false;
    }
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

  // statement ::= [ label ':' ] { attribute_instance } statement_item;
  // statement_or_null and function_statement_or_null additionally permit
  // { attribute_instance } ';'. Enter the item child after its prefix.
  auto parseAttributedStatementRule(std::string_view root) -> bool {
    if (!at(TK::OpenParenthesis) || !at(TK::Star, 1)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = true;
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      valid = consumeAnnexRule("attribute_instance", line_);
      parseGrammarChildDirectiveLines();
    } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
    if (valid && parseAttributeMacroInterruptionRule()) {
      return true;
    }
    if (valid && at(TK::Semicolon) &&
        (root == "statement_or_null" || root == "function_statement_or_null")) {
      consumeInto(line_);
      addLine();
      return true;
    }
    if (valid && !at(TK::Semicolon) && !at(TK::EndOfFile) &&
        !matchingOpenFrame(peek().kind) &&
        !(stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(peek()))) {
      const size_t before = pos_;
      grammar_contexts_.push_back({block_stack_.size(), {"statement_item"}});
      parseStatement();
      grammar_contexts_.pop_back();
      if (pos_ > before) {
        return true;
      }
    }
    recordGrammarFallback("invalid Annex A attributed statement");
    recoverMalformedItem(saved);
    return true;
  }

  // statement_or_null and function_statement_or_null have an independent
  // empty-statement alternative. A nonnullable statement cannot consume ';'.
  auto parseNullStatementRule(std::string_view root) -> bool {
    if (!at(TK::Semicolon) ||
        (root != "statement_or_null" && root != "function_statement_or_null")) {
      return false;
    }
    consumeInto(line_);
    addLine();
    return true;
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
    if (at(TK::Identifier) && at(TK::Colon, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      if (!consumeAnnexRule("generate_block_identifier", line_, TK::Colon) ||
          !at(TK::Colon)) {
        recordGrammarFallback("invalid Annex A generate block label");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!at(TK::BeginKeyword)) {
        recordGrammarFallback("generate block label requires Annex A begin");
        recoverMalformedItem(saved);
        return;
      }
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

  auto markStatementPhase() -> void {
    if (block_stack_.empty()) {
      return;
    }
    switch (block_stack_.back().close_kind) {
      case TK::EndFunctionKeyword:
      case TK::EndTaskKeyword:
      case TK::EndKeyword:
      case TK::JoinKeyword:
        block_stack_.back().statement_phase = true;
        break;
      default:
        break;
    }
  }

  // Enter the production selected by the enclosing rule. During a live
  // conditional continuation the enclosing chart stays active; the same
  // production functions still choose the construction to parse.
  auto parseDirectGrammarRule(bool active_continuation = false) -> bool {
    if (!active_continuation && !grammar_scopes_.empty() &&
        !grammar_paused_.back()) {
      return false;
    }
    const auto roots = grammarRoots();
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const bool declaration =
          std::ranges::any_of(roots, [](std::string_view root) {
            return root == "block_item_declaration" ||
                   root == "tf_item_declaration";
          });
      const auto statement =
          std::ranges::find_if(roots, [](std::string_view root) {
            return root == "statement_or_null" ||
                   root == "function_statement_or_null";
          });
      if (declaration && statement != roots.end()) {
        const auto child = afterAttributePrefix();
        if (child) {
          const TK first = peek(*child).kind;
          const auto after_type = first == TK::Identifier
                                      ? afterUserTypePrefix(*child)
                                      : std::nullopt;
          const bool identifier_statement =
              after_type && !at(TK::Identifier, *after_type) &&
              !at(TK::Semicolon, *after_type) && !at(TK::Comma, *after_type);
          const bool distinct_statement =
              annexCanStart(*statement, first) &&
              !annexCanStart("block_item_declaration", first) &&
              !annexCanStart("tf_item_declaration", first);
          if ((identifier_statement || distinct_statement) &&
              parseAttributedStatementRule(*statement)) {
            markStatementPhase();
            return true;
          }
        }
      }
    }
    for (const std::string_view root : roots) {
      const bool enclosing_attributes =
          at(TK::OpenParenthesis) && at(TK::Star, 1) &&
          (root == "package_item" || root == "checker_or_generate_item");
      if (!enclosing_attributes && !annexCanStart(root, peek().kind)) {
        continue;
      }
      if (root == "library_description" && parseLibraryDescriptionRule()) {
        return true;
      }
      if (root == "timeunits_declaration" && parseTimeunitsRule()) {
        return true;
      }
      if (root == "local_parameter_declaration") {
        if (parseParameterDeclarationRule()) {
          return true;
        }
      }
      if (root == "design_statement") {
        if (parseDesignStatementRule()) {
          return true;
        }
      }
      if (root == "config_rule_statement") {
        if (parseConfigRuleStatementRule()) {
          return true;
        }
      }
      if (root == "description" && block_stack_.empty()) {
        if (parseDescriptionRule()) {
          return true;
        }
      }
      if (root == "generate_block") {
        parseGenerateBlockRule();
        return true;
      }
      if (root == "statement_or_null" || root == "statement" ||
          root == "function_statement_or_null" ||
          root == "function_statement") {
        if (parseNullStatementRule(root) ||
            parseAttributedStatementRule(root) ||
            parseStatementLabelRule(roots) || parseQualifiedStatementRule() ||
            parseStatementItemRule() || parseAssignmentOrCallStatementRule()) {
          markStatementPhase();
          return true;
        }
      }
      if (root == "concurrent_assertion_statement") {
        if (parseConcurrentAssertionRule()) {
          return true;
        }
      }
      if (root == "deferred_immediate_assertion_statement") {
        if (parseImmediateAssertionRule()) {
          return true;
        }
      }
      if (root == "statement_item") {
        if (parseQualifiedStatementRule() || parseStatementItemRule() ||
            parseAssignmentOrCallStatementRule()) {
          markStatementPhase();
          return true;
        }
      }
      if (root == "module_item" || root == "non_port_module_item") {
        if (parseModuleItemRule(root == "module_item")) {
          return true;
        }
      }
      if (root == "interface_item" || root == "non_port_interface_item") {
        if (parseInterfaceItemRule(root == "interface_item")) {
          return true;
        }
      }
      if (root == "program_item" || root == "non_port_program_item") {
        if (parseProgramItemRule(root == "program_item")) {
          return true;
        }
      }
      if (root == "generate_item") {
        if (parseGenerateItemRule()) {
          return true;
        }
      }
      if (root == "checker_or_generate_item") {
        if (parseCheckerItemRule()) {
          return true;
        }
      }
      if (root == "package_item") {
        if (parsePackageItemRule()) {
          return true;
        }
      }
      if (root == "anonymous_program_item") {
        if (parseAnonymousProgramItemRule()) {
          return true;
        }
      }
      if (root == "class_item") {
        if (parseClassItemRule()) {
          return true;
        }
      }
      if (root == "interface_class_item") {
        if (parseInterfaceClassItemRule()) {
          return true;
        }
      }
      if (root == "constraint_block_item" && parseConstraintBlockItemRule()) {
        return true;
      }
      if (root == "constraint_expression") {
        if (parseConstraintExpressionRule()) {
          return true;
        }
      }
      if (root == "rs_production") {
        parseRsProductionRule();
        return true;
      }
      if (root == "clocking_item") {
        if (parseClockingItemRule()) {
          return true;
        }
      }
      if (root == "specify_item") {
        if (parseSpecifyItemRule()) {
          return true;
        }
      }
      if (root == "coverage_spec_or_option") {
        if (parseCoverageSpecOrOptionRule()) {
          return true;
        }
      }
      if (root == "bins_or_options") {
        if (parseBinsOrOptionsRule()) {
          return true;
        }
        parseAnnexSemicolonItem("bins_or_options");
        return true;
      }
      if (root == "cross_body_item" && parseCrossBodyItemRule()) {
        return true;
      }
      if (root == "tf_item_declaration" || root == "block_item_declaration") {
        if (parseBlockOrTfItemDeclarationRule(root == "tf_item_declaration")) {
          return true;
        }
      }
    }
    return false;
  }

  // A parent production can be waiting for a complete item. Let that item's
  // production function parse and emit it directly, then advance the parent
  // over the completed nonterminal. If the function has no matching
  // alternative, the caller retains the parent chart for an ambiguous leaf.
  auto parseDirectChildRule() -> bool {
    if (grammar_scopes_.empty() || grammar_paused_.back() ||
        grammar_scopes_.back().failed || grammar_scopes_.back().interrupted) {
      return false;
    }
    const auto roots = grammarRoots();
    std::vector<uint16_t> candidates;
    const auto& waiting = grammar_scopes_.back().charts.back().waiting;
    for (const auto root : roots) {
      if (!annexCanStart(root, peek().kind)) {
        continue;
      }
      const int rule = annexRule(root);
      if (rule < 0 || !waiting.contains(static_cast<uint16_t>(rule))) {
        return false;
      }
      candidates.push_back(static_cast<uint16_t>(rule));
    }
    if (candidates.empty()) {
      return false;
    }
    const AnnexState::Checkpoint checkpoint =
        grammar_scopes_.back().checkpoint();
    const size_t start = pos_;
    const size_t output_size = lines_.size();
    const size_t line_tokens = line_.tokens.size();
    const size_t block_depth = block_stack_.size();
    grammar_paused_.back() = true;
    if (!parseDirectGrammarRule(true)) {
      grammar_paused_.back() = false;
      if (pos_ != start || lines_.size() != output_size ||
          line_.tokens.size() != line_tokens) {
        grammar_scopes_.back().interrupted = true;
        recordGrammarFallback(
            "direct Annex A child rejected after consuming tokens");
        return true;
      }
      return false;
    }
    grammar_paused_.back() = false;
    if (block_stack_.size() != block_depth) {
      grammar_scopes_.back().interrupted = true;
      recordGrammarFallback("direct Annex A child lost its closing boundary");
      return true;
    }
    if (!grammar_scopes_.back().skipOpaqueItem(checkpoint, candidates)) {
      recordGrammarFallback("Annex A parent cannot resume after child");
    }
    return true;
  }

  auto parseStatement() -> void {
    const bool top_level = grammar_contexts_.empty() && block_stack_.empty() &&
                           peek().kind != TK::Directive;
    const size_t start = pos_;
    const uint8_t next_modes =
        top_level ? nextSourceModes(peek().kind) : source_modes_;
    if (top_level && !next_modes) {
      recordGrammarFallback("item outside Annex A source_text or library_text");
    }
    parseStatementImpl();
    if (top_level && next_modes && pos_ > start) {
      source_modes_ = next_modes;
    }
  }

  auto parseStatementImpl() -> void {
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

    // Let a direct Annex A item rule consume its own attribute_instance
    // children. Keep the shared prefix path for roots whose direct rule does
    // not yet include attributes (and for description/package prefixes).
    if (at(TK::OpenParenthesis) && at(TK::Star, 1) &&
        parseDirectGrammarRule()) {
      return;
    }

    // package_declaration stores these outside package_item; other remaining
    // contexts validate them through their current root.
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const bool package_item =
          !block_stack_.empty() &&
          block_stack_.back().grammar_body == "package_item";
      const auto roots = grammarRoots();
      const bool allowed =
          package_item || std::ranges::any_of(roots, [](std::string_view root) {
            return annexCanStart(root, TK::OpenParenthesis);
          });
      if (!allowed || !consumeAnnexRule("attribute_instance", line_)) {
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

    if (!at(TK::BeginKeyword)) {
      pending_if_begin_ = false;
    }

    if (!block_stack_.empty() && block_stack_.back().constructor_body &&
        at(TK::SuperKeyword) && at(TK::Dot, 1) && at(TK::NewKeyword, 2)) {
      parseConstructorSuperRule();
      return;
    }

    if (grammar_scopes_.empty() && block_stack_.empty() &&
        (static_cast<unsigned>(source_modes_) &
         (static_cast<unsigned>(kSourceBeforeDescription) |
          static_cast<unsigned>(kSourceAfterTimeunits) |
          static_cast<unsigned>(kSourceAfterDescription))) &&
        parseDescriptionRule()) {
      return;
    }
    if (parseDirectGrammarRule()) {
      return;
    }
    if (parseDirectChildRule()) {
      return;
    }

    if (!block_stack_.empty() &&
        block_stack_.back().grammar_body == "udp_body") {
      parseUdpBodyItem();
      return;
    }
    if (!block_stack_.empty() &&
        block_stack_.back().grammar_body == "udp_table_entry") {
      parseUdpTableEntryRule();
      return;
    }

    // Shared-prefix leaves keep an item chart while their tokens are emitted.
    beginGrammar(grammarRoots(), true);
    summarizeChildInParent();
    parseLeafLayout(grammar_scopes_.back());
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

  auto parseLeafLayout(const AnnexState& selector) -> void {
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
    if (first == TK::MacroUsage) {
      recordGrammarFallback("macro expansion unavailable to Annex A");
      grammar_scopes_.back().interrupted = true;
      parseMacroItem();
    } else if (first == TK::Identifier && grammarAllows(first)) {
      parseIdentifierItem();
    } else if (const auto block = blockSpec(first);
               block && !grammarAllows(first)) {
      recordGrammarFallback("block outside the current Annex A body rule");
      const auto after = findPairedEnd(pos_, block->close_kind);
      emitOpaque(pos_, after ? *after : findOuterBoundary(pos_));
    } else if (!grammarAllows(first)) {
      recordGrammarFallback("item is outside this Annex A body rule");
      // A terminal that begins some Annex A production is a malformed item in
      // this context. Its semicolon is a useful recovery point. Tokens that
      // begin no production need the enclosing block's closing boundary.
      constexpr std::array item_rules = {"module_item",
                                         "interface_item",
                                         "program_item",
                                         "package_item",
                                         "class_item",
                                         "statement_or_null",
                                         "generate_item",
                                         "checker_or_generate_item",
                                         "clocking_item",
                                         "specify_item",
                                         "coverage_spec_or_option",
                                         "constraint_expression"};
      const bool annex_item_start =
          std::ranges::any_of(item_rules, [first](std::string_view rule) {
            return annexCanStart(rule, first);
          });
      if (annex_item_start) {
        grammar_scopes_.back().interrupted = true;
        consumeUntilSemi();
      } else {
        emitOpaque(pos_, findOuterBoundary(pos_));
      }
    } else {
      parseGrammarLeaf();
    }
  }

  auto parseLabeledStatement(std::string_view body_rule) -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // label identifier
    consumeInto(line_);  // colon
    if (body_rule == "statement_item") {
      parseGrammarChildDirectiveLines();
      while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
        if (!consumeAnnexRule("attribute_instance", line_)) {
          recordGrammarFallback("invalid Annex A labeled statement attribute");
          recoverMalformedItem(saved);
          return;
        }
        parseGrammarChildDirectiveLines();
      }
    }
    if (matchingOpenFrame(peek().kind) || at(TK::EndOfFile)) {
      recordGrammarFallback("missing Annex A labeled statement item");
      recoverMalformedItem(saved);
      return;
    }
    const auto checkpoint =
        grammar_scopes_.empty()
            ? std::optional<AnnexState::Checkpoint>{}
            : std::optional{grammar_scopes_.back().checkpoint()};
    const bool was_paused = checkpoint && grammar_paused_.back();
    if (checkpoint) {
      grammar_paused_.back() = true;
    }
    grammar_contexts_.push_back({block_stack_.size(), {body_rule}});
    parseStatement();
    grammar_contexts_.pop_back();
    if (!checkpoint) {
      return;
    }
    grammar_paused_.back() = was_paused;
    if (!grammar_scopes_.back().skipOpaqueItem(
            *checkpoint, {static_cast<uint16_t>(annexRule(body_rule))})) {
      recordGrammarFallback("labeled Annex A statement cannot resume");
    }
  }

  // action_block ::= statement_or_null |
  // [ statement ] 'else' statement_or_null. A recursive statement call owns
  // any nested else before this production considers its own else.
  auto parseActionBlockRule() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    parseGrammarChildDirectiveLines();
    const auto after_attributes = afterAttributePrefix();
    const bool null_before_else =
        after_attributes && at(TK::Semicolon, *after_attributes);
    if (!at(TK::ElseKeyword)) {
      if (atEnclosingBoundary()) {
        recordGrammarFallback("missing Annex A action block statement");
        return;
      }
      grammar_contexts_.push_back({block_stack_.size(), {"statement_or_null"}});
      parseStatement();
      grammar_contexts_.pop_back();
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::ElseKeyword)) {
      return;
    }
    if (null_before_else) {
      recordGrammarFallback(
          "Annex A action_block requires a statement before else");
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (atEnclosingBoundary()) {
      recordGrammarFallback("missing Annex A action block else statement");
      recoverMalformedItem(saved);
      return;
    }
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
    if (parseConcurrentAssertionRule()) {
      return true;
    }
    if ((at(TK::AssertKeyword) || at(TK::AssumeKeyword) ||
         at(TK::CoverKeyword)) &&
        (at(TK::Hash, 1) || at(TK::FinalKeyword, 1))) {
      return parseImmediateAssertionRule();
    }
    return false;
  }

  auto parseRestrictPropertyStatementRule() -> bool {
    if (!at(TK::RestrictKeyword) || !at(TK::PropertyKeyword, 1)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // restrict
    consumeInto(line_);  // property
    if (!at(TK::OpenParenthesis)) {
      recordGrammarFallback("invalid Annex A restrict property header");
      recoverMalformedItem(saved);
      return true;
    }
    const bool property_spec = consumeAnnexDelimited(
        TK::OpenParenthesis, TK::CloseParenthesis, "property_spec", line_);
    if (!property_spec && !unavailableMacroIn(saved.pos, pos_)) {
      recoverMalformedItem(saved);
      return true;
    }
    if (line_.tokens.empty() ||
        line_.tokens.back().kind != TK::CloseParenthesis ||
        !at(TK::Semicolon)) {
      recordGrammarFallback("incomplete Annex A restrict property");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseAssertPropertyStatementRule() -> bool {
    if ((!at(TK::AssertKeyword) && !at(TK::AssumeKeyword)) ||
        !at(TK::PropertyKeyword, 1)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // assert / assume
    consumeInto(line_);  // property
    if (!at(TK::OpenParenthesis)) {
      recordGrammarFallback("invalid Annex A property assertion header");
      recoverMalformedItem(saved);
      return true;
    }
    const bool property_spec = consumeAnnexDelimited(
        TK::OpenParenthesis, TK::CloseParenthesis, "property_spec", line_);
    if (!property_spec && !unavailableMacroIn(saved.pos, pos_)) {
      recoverMalformedItem(saved);
      return true;
    }
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
    if (rule == "cover_property_statement") {
      consumeInto(line_);  // cover
      consumeInto(line_);  // property
      if (!at(TK::OpenParenthesis)) {
        recordGrammarFallback("invalid Annex A cover property header");
        recoverMalformedItem(saved);
        return true;
      }
      const bool property_spec = consumeAnnexDelimited(
          TK::OpenParenthesis, TK::CloseParenthesis, "property_spec", line_);
      if (!property_spec && !unavailableMacroIn(saved.pos, pos_)) {
        recoverMalformedItem(saved);
        return true;
      }
      if (line_.tokens.empty() ||
          line_.tokens.back().kind != TK::CloseParenthesis) {
        recordGrammarFallback("incomplete Annex A cover property");
        recoverMalformedItem(saved);
        return true;
      }
      grammar_contexts_.push_back({block_stack_.size(), {"statement_or_null"}});
      parseStatement();
      grammar_contexts_.pop_back();
      return true;
    }
    beginGrammar({rule});
    while (!at(TK::EndOfFile) &&
           !grammar_scopes_.back().hasActiveRule("statement_or_null")) {
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
      if (!grammar_scopes_.back().accepts(peek().kind)) {
        break;
      }
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
  auto parseConditionalImmediateAssertionRule() -> bool {
    if (!at(TK::AssertKeyword) && !at(TK::AssumeKeyword) &&
        !at(TK::CoverKeyword)) {
      return false;
    }
    if (at(TK::PropertyKeyword, 1) || at(TK::SequenceKeyword, 1)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"immediate_assertion_statement"});
    while (!at(TK::EndOfFile) &&
           !grammar_scopes_.back().hasActiveRule("action_block") &&
           !grammar_scopes_.back().hasActiveRule("statement_or_null")) {
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
      if (!grammar_scopes_.back().accepts(peek().kind)) {
        break;
      }
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

  auto parseImmediateAssertionRule() -> bool {
    if (!at(TK::AssertKeyword) && !at(TK::AssumeKeyword) &&
        !at(TK::CoverKeyword)) {
      return false;
    }
    if (at(TK::PropertyKeyword, 1) || at(TK::SequenceKeyword, 1)) {
      return false;
    }
    if (isConditionalStartDirective(peek(1))) {
      return parseConditionalImmediateAssertionRule();
    }

    const LeafCheckpoint saved = leafCheckpoint();
    const bool cover = at(TK::CoverKeyword);
    consumeInto(line_);
    if (at(TK::Hash)) {
      consumeInto(line_);
      if (!at(TK::IntegerLiteral) || peek().rawText() != "0") {
        recordGrammarFallback("invalid Annex A deferred assertion #0");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
    } else if (at(TK::FinalKeyword)) {
      consumeInto(line_);
    }
    if (!at(TK::OpenParenthesis)) {
      recordGrammarFallback("invalid Annex A immediate assertion header");
      recoverMalformedItem(saved);
      return true;
    }
    const bool expression = consumeAnnexDelimited(
        TK::OpenParenthesis, TK::CloseParenthesis, "expression", line_);
    if (!expression && !unavailableMacroIn(saved.pos, pos_)) {
      recoverMalformedItem(saved);
      return true;
    }
    if (line_.tokens.empty() ||
        line_.tokens.back().kind != TK::CloseParenthesis) {
      recordGrammarFallback("incomplete Annex A immediate assertion");
      recoverMalformedItem(saved);
      return true;
    }
    if (cover) {
      grammar_contexts_.push_back({block_stack_.size(), {"statement_or_null"}});
      parseStatement();
      grammar_contexts_.pop_back();
    } else {
      parseActionBlockRule();
    }
    return true;
  }

  // expect_property_statement ::= 'expect' '(' property_spec ')' action_block.
  auto parseExpectPropertyStatementRule() -> bool {
    if (!at(TK::ExpectKeyword)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    if (!at(TK::OpenParenthesis)) {
      recordGrammarFallback("invalid Annex A expect header");
      recoverMalformedItem(saved);
      return true;
    }
    const bool property_spec = consumeAnnexDelimited(
        TK::OpenParenthesis, TK::CloseParenthesis, "property_spec", line_);
    if (!property_spec && !unavailableMacroIn(saved.pos, pos_)) {
      recoverMalformedItem(saved);
      return true;
    }
    if (line_.tokens.empty() ||
        line_.tokens.back().kind != TK::CloseParenthesis) {
      recordGrammarFallback("incomplete Annex A expect property");
      recoverMalformedItem(saved);
      return true;
    }
    parseActionBlockRule();
    return true;
  }

  // module_instantiation / interface_instantiation /
  // program_instantiation ::= structural_identifier
  // [ parameter_value_assignment ] hierarchical_instance
  // { ',' hierarchical_instance } ';'. Shared identifier prefixes that do
  // not have the instance shape stay with their local declaration chart.
  [[nodiscard]] auto unavailableInFollowingParentheses(size_t start) const
      -> bool {
    int depth = 0;
    int brackets = 0;
    for (size_t i = start; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        return true;
      }
      if (token.kind == TK::OpenBracket) {
        ++brackets;
      }
      if (token.kind == TK::CloseBracket && brackets > 0) {
        --brackets;
      }
      if (brackets == 0 && token.kind == TK::OpenParenthesis) {
        ++depth;
      }
      if (brackets == 0 && token.kind == TK::CloseParenthesis && depth > 0) {
        --depth;
        if (depth != 0) {
          continue;
        }
        break;
      }
      if (token.kind == TK::EndOfFile) {
        break;
      }
    }
    return false;
  }

  // named_parameter_assignment ::= '.' parameter_identifier '('
  //                                 [ param_expression ] ')'.
  [[nodiscard]] auto parseNamedParameterAssignmentRule() -> bool {
    if (!at(TK::Dot)) {
      return false;
    }
    consumeInto(line_);
    if (!consumeAnnexRule("parameter_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis) &&
        !consumeAnnexRule("param_expression", line_, TK::CloseParenthesis)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // ordered_parameter_assignment ::= param_expression.
  [[nodiscard]] auto parseOrderedParameterAssignmentRule() -> bool {
    return consumeAnnexRule("param_expression", line_, TK::Comma);
  }

  [[nodiscard]] auto parseParameterValueAssignmentRule() -> bool {
    if (!at(TK::Hash) || !at(TK::OpenParenthesis, 1)) {
      return false;
    }
    consumeInto(line_);
    consumeInto(line_);
    addLine();
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis)) {
      const bool named = at(TK::Dot);
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        parseGrammarChildDirectiveLines();
        if (at(TK::Dot) != named) {
          return false;
        }
        if (!(named ? parseNamedParameterAssignmentRule()
                    : parseOrderedParameterAssignmentRule())) {
          return false;
        }
        parseGrammarChildDirectiveLines();
        if (!at(TK::Comma)) {
          break;
        }
        consumeInto(line_);
        addLine();
      } while (!at(TK::EndOfFile));
    }
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    addLine();
    consumeInto(line_);
    return true;
  }

  auto parseGrammarChildDirectiveLines() -> void {
    while (isCompilerDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
  }

  // named_port_connection and named_checker_port_connection share this
  // punctuation after their attribute_instance prefix.
  [[nodiscard]] auto parseNamedPortConnectionRule(bool& module_possible,
                                                  bool& checker_possible)
      -> bool {
    if (!at(TK::Dot)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (at(TK::Star)) {
      consumeInto(line_);
      return true;
    }
    if (!consumeAnnexRule("port_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::OpenParenthesis)) {
      return true;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis) &&
        !parseSharedPortActualRule(module_possible, checker_possible)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // ordered_port_connection and ordered_checker_port_connection both allow
  // an empty argument after their attribute_instance prefix.
  [[nodiscard]] auto parseOrderedPortConnectionRule(bool& module_possible,
                                                    bool& checker_possible)
      -> bool {
    return at(TK::Comma) || at(TK::CloseParenthesis) ||
           parseSharedPortActualRule(module_possible, checker_possible);
  }

  // Module and checker connections share their punctuation. Only the actual
  // argument differs: expression versus property_actual_arg. Keep a local
  // grammar choice for that child and update the two enclosing alternatives.
  [[nodiscard]] auto parseSharedPortActualRule(bool& module_possible,
                                               bool& checker_possible) -> bool {
    std::vector<std::string_view> rules;
    if (module_possible) {
      rules.emplace_back("expression");
    }
    if (checker_possible) {
      rules.emplace_back("property_actual_arg");
    }
    if (rules.empty()) {
      return false;
    }
    beginGrammar(rules);
    ListDepth depth;
    while (!at(TK::EndOfFile)) {
      if (depth.topLevel() && (at(TK::Comma) || at(TK::CloseParenthesis))) {
        break;
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
          ++depth.parens;
          break;
        case TK::CloseParenthesis:
          --depth.parens;
          break;
        case TK::OpenBracket:
          ++depth.brackets;
          break;
        case TK::CloseBracket:
          --depth.brackets;
          break;
        case TK::OpenBrace:
        case TK::ApostropheOpenBrace:
          ++depth.braces;
          break;
        case TK::CloseBrace:
          --depth.braces;
          break;
        default:
          break;
      }
      consumeInto(line_);
    }
    const AnnexState actual = endGrammar(false);
    if (actual.failed || actual.interrupted || !actual.complete()) {
      return false;
    }
    module_possible &= actual.completed("expression");
    checker_possible &= actual.completed("property_actual_arg");
    return module_possible || checker_possible;
  }

  [[nodiscard]] auto parseSharedPortConnectionRule(
      bool& named,  // NOLINT(bugprone-easily-swappable-parameters)
      bool& style_selected, bool& module_possible, bool& checker_possible)
      -> bool {
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    const bool item_named = at(TK::Dot);
    if (!style_selected) {
      named = item_named;
      style_selected = true;
    }
    if (item_named != named) {
      return false;
    }
    return named
               ? parseNamedPortConnectionRule(module_possible, checker_possible)
               : parseOrderedPortConnectionRule(module_possible,
                                                checker_possible);
  }

  [[nodiscard]] auto parseHierarchicalInstanceRule(
      bool allow_checker,
      bool& checker_only,  // NOLINT(bugprone-easily-swappable-parameters)
      bool& checker_viable) -> bool {
    if (!consumeAnnexRule("name_of_instance", line_) ||
        !at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    addLine();
    bool module_possible = true;
    bool checker_possible = allow_checker;
    if (!at(TK::CloseParenthesis)) {
      bool named = false;
      bool style_selected = false;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        if (!parseSharedPortConnectionRule(named, style_selected,
                                           module_possible, checker_possible)) {
          return false;
        }
        parseGrammarChildDirectiveLines();
        if (!at(TK::Comma)) {
          break;
        }
        consumeInto(line_);
        addLine();
      } while (!at(TK::EndOfFile));
    }
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    addLine();
    consumeInto(line_);
    checker_only = checker_possible && !module_possible;
    checker_viable = checker_possible;
    return true;
  }

  [[nodiscard]] auto hasInstanceShape(size_t index) const -> bool {
    if (index < pos_ || index >= tokens_.size()) {
      return false;
    }
    const size_t offset = index - pos_;
    if (!at(TK::Identifier, offset)) {
      return false;
    }
    const auto after_dimensions = afterBalancedDimensions(offset + 1);
    return after_dimensions && at(TK::OpenParenthesis, *after_dimensions);
  }

  auto parseScopedCheckerInstantiationRule(bool finish_line = true,
                                           bool* valid_result = nullptr)
      -> bool {
    if (valid_result) {
      *valid_result = false;
    }
    if ((!at(TK::Identifier) && !at(TK::UnitSystemName)) ||
        !at(TK::DoubleColon, 1) || !at(TK::Identifier, 2) ||
        !hasInstanceShape(pos_ + 3)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool checker_only = false;
    bool checker_viable = false;
    if (!consumeAnnexRule("ps_checker_identifier", line_) ||
        !parseHierarchicalInstanceRule(true, checker_only, checker_viable) ||
        !checker_viable || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A scoped checker instantiation");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    if (finish_line) {
      addLine();
    }
    if (valid_result) {
      *valid_result = true;
    }
    return true;
  }

  // A.3.1 fixes the terminal order for these primitive instances. The
  // n_output_gate_instance list has a shared comma prefix between its final
  // output and input, so that one keeps its local Annex A child state.
  [[nodiscard]] auto parseGateInstanceRule(std::string_view instance) -> bool {
    if (instance == "n_output_gate_instance") {
      return consumeAnnexRule(instance, line_, TK::Comma);
    }
    if (at(TK::Identifier) && !consumeAnnexRule("name_of_instance", line_)) {
      return false;
    }
    while (afterOrdinaryDirectives(0) > 0) {
      addLine();
      parseDirectiveLine();
    }
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    const auto terminal = [&](std::string_view rule) -> bool {
      parseGrammarChildDirectiveLines();
      return consumeAnnexRule(rule, line_, TK::Comma,
                              [&] { return at(TK::CloseParenthesis); });
    };
    const auto separator = [&]() -> bool {
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        return false;
      }
      consumeInto(line_);
      return true;
    };
    const bool pass = instance == "pass_switch_instance" ||
                      instance == "pass_enable_switch_instance";
    bool valid = terminal(pass ? "inout_terminal" : "output_terminal");
    if (instance == "pull_gate_instance") {
      // pull_gate_instance ::= [ name_of_instance ] '(' output_terminal ')'.
    } else if (valid && separator()) {
      valid = terminal(pass ? "inout_terminal" : "input_terminal");
    } else {
      valid = false;
    }
    if (valid && instance == "n_input_gate_instance") {
      while (at(TK::Comma)) {
        consumeInto(line_);
        valid = terminal("input_terminal");
        if (!valid) {
          break;
        }
      }
    } else if (valid && instance != "pass_switch_instance" &&
               instance != "pull_gate_instance") {
      if (!separator()) {
        return false;
      }
      const std::string_view third = instance == "cmos_switch_instance"
                                         ? "ncontrol_terminal"
                                         : "enable_terminal";
      valid = terminal(third);
      if (valid && instance == "cmos_switch_instance") {
        valid = separator() && terminal("pcontrol_terminal");
      }
    }
    parseGrammarChildDirectiveLines();
    if (!valid || !at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // gate_instantiation has eight alternatives selected by distinct Annex A
  // gate type terminals. Each instance is a child of the selected production.
  [[nodiscard]] auto parseGateInstantiationRule() -> bool {
    std::string_view type;
    std::string_view instance;
    std::string_view delay;
    std::string_view strength;
    if (annexCanStart("cmos_switchtype", peek().kind)) {
      type = "cmos_switchtype";
      instance = "cmos_switch_instance";
      delay = "delay3";
    } else if (annexCanStart("mos_switchtype", peek().kind)) {
      type = "mos_switchtype";
      instance = "mos_switch_instance";
      delay = "delay3";
    } else if (annexCanStart("enable_gatetype", peek().kind)) {
      type = "enable_gatetype";
      instance = "enable_gate_instance";
      delay = "delay3";
      strength = "drive_strength";
    } else if (annexCanStart("n_input_gatetype", peek().kind)) {
      type = "n_input_gatetype";
      instance = "n_input_gate_instance";
      delay = "delay2";
      strength = "drive_strength";
    } else if (annexCanStart("n_output_gatetype", peek().kind)) {
      type = "n_output_gatetype";
      instance = "n_output_gate_instance";
      delay = "delay2";
      strength = "drive_strength";
    } else if (annexCanStart("pass_en_switchtype", peek().kind)) {
      type = "pass_en_switchtype";
      instance = "pass_enable_switch_instance";
      delay = "delay2";
    } else if (annexCanStart("pass_switchtype", peek().kind)) {
      type = "pass_switchtype";
      instance = "pass_switch_instance";
    } else if (at(TK::PullDownKeyword) || at(TK::PullUpKeyword)) {
      const bool down = at(TK::PullDownKeyword);
      type = down ? "pulldown" : "pullup";
      instance = "pull_gate_instance";
      strength = down ? "pulldown_strength" : "pullup_strength";
    } else {
      return false;
    }
    if (hasAnnexListInterruption(pos_, false)) {
      static_cast<void>(parseAnnexItem({"gate_instantiation"}, true));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    bool valid = true;
    if (type == "pulldown" || type == "pullup") {
      consumeInto(line_);
    } else {
      valid = consumeAnnexRule(type, line_);
    }
    skip_directives();
    const bool has_strength =
        valid && !strength.empty() && at(TK::OpenParenthesis) &&
        (annexCanStart("strength0", peek(1).kind) ||
         annexCanStart("strength1", peek(1).kind) || at(TK::HighZ0Keyword, 1) ||
         at(TK::HighZ1Keyword, 1));
    if (has_strength) {
      valid = consumeAnnexRule(strength, line_);
    }
    skip_directives();
    if (valid && !delay.empty() && at(TK::Hash)) {
      valid = consumeAnnexRule(delay, line_);
    }
    skip_directives();
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!valid) {
        break;
      }
      parseGrammarChildDirectiveLines();
      valid = parseGateInstanceRule(instance);
      parseGrammarChildDirectiveLines();
      if (!valid || !at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
      addLine();
    } while (true);
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A gate instantiation");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // The immediate '(' of an unnamed UDP instance or drive_strength, and a
  // non-parenthesized delay2, distinguish these forms from module instances.
  [[nodiscard]] auto parseUdpInstantiationRule() -> bool {
    const size_t after_identifier = afterOrdinaryDirectives(1);
    if (!at(TK::Identifier) ||
        !(at(TK::OpenParenthesis, after_identifier) ||
          (at(TK::Hash, after_identifier) &&
           !at(TK::OpenParenthesis,
               afterOrdinaryDirectives(after_identifier + 1))))) {
      return false;
    }
    if (hasAnnexListInterruption(pos_, false)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    bool valid = consumeAnnexRule("udp_identifier", line_);
    skip_directives();
    const bool strength =
        valid && at(TK::OpenParenthesis) &&
        (annexCanStart("strength0", peek(1).kind) ||
         annexCanStart("strength1", peek(1).kind) || at(TK::HighZ0Keyword, 1) ||
         at(TK::HighZ1Keyword, 1));
    if (valid && strength) {
      valid = consumeAnnexRule("drive_strength", line_);
    }
    skip_directives();
    if (valid && at(TK::Hash)) {
      valid = consumeAnnexRule("delay2", line_);
    }
    skip_directives();
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!valid) {
        break;
      }
      parseGrammarChildDirectiveLines();
      if (at(TK::Identifier)) {
        valid = consumeAnnexRule("name_of_instance", line_);
      }
      skip_directives();
      if (!valid || !at(TK::OpenParenthesis)) {
        valid = false;
        break;
      }
      consumeInto(line_);
      addLine();
      valid = consumeAnnexRule("output_terminal", line_, TK::Comma);
      if (!valid || !at(TK::Comma)) {
        valid = false;
        break;
      }
      consumeInto(line_);
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        parseGrammarChildDirectiveLines();
        valid = consumeAnnexRule("input_terminal", line_, TK::Comma,
                                 [&] { return at(TK::CloseParenthesis); });
        if (!valid || !at(TK::Comma)) {
          break;
        }
        consumeInto(line_);
      } while (true);
      if (!valid || !at(TK::CloseParenthesis)) {
        valid = false;
        break;
      }
      addLine();
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
      addLine();
    } while (true);
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A UDP instantiation");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseStructuralInstantiationRule(bool finish_line = true,
                                        bool* valid_result = nullptr) -> bool {
    if (valid_result) {
      *valid_result = false;
    }
    if (!at(TK::Identifier) && !at(TK::UnitSystemName)) {
      return false;
    }
    if (at(TK::DoubleColon, 1)) {
      return parseScopedCheckerInstantiationRule(finish_line, valid_result);
    }
    bool instance_shape = hasInstanceShape(pos_ + 1);
    if (at(TK::Hash, 1) && at(TK::OpenParenthesis, 2)) {
      const auto after_parameters = afterBalancedParentheses(2);
      instance_shape =
          after_parameters && hasInstanceShape(pos_ + *after_parameters);
    }
    if (!instance_shape) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    if (!consumeAnnexRule("module_identifier", line_)) {
      recordGrammarFallback("invalid Annex A module identifier");
      recoverMalformedItem(saved);
      return true;
    }
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    const bool parameterized = at(TK::Hash);
    if (at(TK::Hash)) {
      bool valid = false;
      if (unavailableInFollowingParentheses(pos_ + 1)) {
        beginGrammar({"parameter_value_assignment"});
        consumeInto(line_);
        static_cast<void>(parseParenthesizedListInto(line_));
        const AnnexState parameters = endGrammar();
        valid = !parameters.failed && !parameters.interrupted &&
                parameters.complete();
      } else {
        valid = parseParameterValueAssignmentRule();
      }
      if (!valid) {
        recordGrammarFallback("invalid Annex A parameter assignment");
        recoverMalformedItem(saved);
        return true;
      }
      skip_directives();
    }
    size_t instance_count = 0;
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      bool valid = false;
      bool checker_only = false;
      bool checker_viable = false;
      if (unavailableInFollowingParentheses(pos_)) {
        beginGrammar({"hierarchical_instance"});
        const bool named = consumeAnnexRule("name_of_instance", line_);
        if (named && at(TK::OpenParenthesis)) {
          static_cast<void>(parseParenthesizedListInto(line_));
        }
        const AnnexState instance = endGrammar();
        valid = named && !instance.failed && !instance.interrupted &&
                instance.complete();
      } else {
        valid = parseHierarchicalInstanceRule(!parameterized, checker_only,
                                              checker_viable);
      }
      if (!valid || (checker_only && instance_count != 0)) {
        recordGrammarFallback("invalid Annex A hierarchical instance");
        recoverMalformedItem(saved);
        return true;
      }
      ++instance_count;
      skip_directives();
      if (checker_only && at(TK::Comma)) {
        recordGrammarFallback("checker instantiation has one Annex A instance");
        recoverMalformedItem(saved);
        return true;
      }
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
      addLine();
      skip_directives();
    } while (true);
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A module instantiation semicolon");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    if (finish_line) {
      addLine();
    }
    if (valid_result) {
      *valid_result = true;
    }
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
          if (!at(TK::Identifier) || !grammarAllows(TK::Identifier)) {
            break;
          }
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
      if (kind == TK::Semicolon && depth == 0) {
        break;
      }
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
        for (size_t i = 0; i < joined->block_stack.size(); ++i) {
          joined->block_stack.at(i).conditional_entry_frame =
              i < branch_entry.block_stack.size()
                  ? branch_entry.block_stack.at(i).conditional_entry_frame
                  : false;
        }
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
        if (depth.parens > 0) {
          --depth.parens;
        }
        break;
      case TK::OpenBracket:
        ++depth.brackets;
        break;
      case TK::CloseBracket:
        if (depth.brackets > 0) {
          --depth.brackets;
        }
        break;
      case TK::ApostropheOpenBrace:
      case TK::OpenBrace:
        ++depth.braces;
        break;
      case TK::CloseBrace:
        if (depth.braces > 0) {
          --depth.braces;
        }
        break;
      default:
        break;
    }
  }

  auto parseParenthesizedListInto(Line& line, TK recovery_close = TK::EndOfFile)
      -> bool {
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
      if (!grammar_scopes_.empty()) {
        grammar_scopes_.back().interrupted = true;
      }
    }
    return had_compiler_directive;
  }

  // module foo #(...) (...); ... endmodule
  // NOLINTBEGIN(bugprone-easily-swappable-parameters)
  auto consumeGrammarHeader(
      TK closeKw, std::initializer_list<std::string_view> boundaryRules,
      std::initializer_list<std::string_view> completedRules = {}) -> void {
    // NOLINTEND(bugprone-easily-swappable-parameters)
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
        if (at(TK::Semicolon)) {
          consumeInto(line_);
        }
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

  auto parseSpecifyBlockRule() -> void {
    consumeInto(line_);
    addLine();
    parseDelimitedBody(TK::EndSpecifyKeyword, "specify_item");
  }

  auto parseAnnexDelimitedBlock(
      TK closeKw,
      std::string_view  // NOLINT(bugprone-easily-swappable-parameters)
          declarationRule,
      std::string_view bodyRule) -> void {
    beginGrammar({declarationRule});
    consumeGrammarHeader(closeKw, {declarationRule});
    const AnnexState header = endGrammar(false);
    const bool global_clocking = declarationRule == "clocking_declaration" &&
                                 header.hasViableProductionStartingWith(
                                     declarationRule, TK::GlobalKeyword);
    if (global_clocking) {
      pushOpenFrame(closeKw);
      ++indent_level_;
      while (isCompilerDirective(peek())) {
        parseDirectiveLine();
      }
      if (!at(closeKw)) {
        recordGrammarFallback("global clocking has no clocking_item body");
        emitOpaque(pos_, findOuterBoundary(pos_));
      }
      if (at(closeKw)) {
        parseOpenFrameClose();
      }
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
      if (indent_level_ > baseIndent) {
        --indent_level_;
      }
    }
    const bool list_separator =
        listDepth && kind == TK::Comma && listDepth->topLevel();
    if (listDepth) {
      advanceListDepth(*listDepth, kind);
    }
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
      if (listDepth) {
        *listDepth = entry_depth;
      }
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
      if (!isConditionalAlternativeDirective(peek())) {
        break;
      }
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
    if (branches.empty()) {
      return false;
    }
    const auto& joined = branches.front();
    for (const auto& branch : branches) {
      bool same_grammar = joined.grammars.size() == branch.grammars.size();
      for (size_t i = 0; same_grammar && i < joined.grammars.size(); ++i) {
        const auto& left = joined.grammars.at(i);
        const auto& right = branch.grammars.at(i);
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
        grammar_scopes_.at(i).addContinuation(
            branches.at(branch).grammars.at(i));
      }
    }
    headerEnded = joined.header_ended;
    indent_level_ = joined.indent;
    if (listDepth) {
      *listDepth = joined.depth;
    }
    return true;
  }

  [[nodiscard]] auto parseAssertionDeclarationHeaderRule(TK closeKw,
                                                         bool conditional_ports)
      -> bool {
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    const std::string_view identifier_rule = closeKw == TK::EndPropertyKeyword
                                                 ? "property_identifier"
                                                 : "sequence_identifier";
    const std::string_view port_item = closeKw == TK::EndPropertyKeyword
                                           ? "property_port_item"
                                           : "sequence_port_item";
    const std::string_view port_list = closeKw == TK::EndPropertyKeyword
                                           ? "property_port_list"
                                           : "sequence_port_list";
    consumeInto(line_);  // property / sequence
    skip_directives();
    if (!consumeAnnexRule(identifier_rule, line_)) {
      return false;
    }
    skip_directives();
    if (at(TK::OpenParenthesis)) {
      consumeInto(line_);
      bool valid = true;
      if (!at(TK::CloseParenthesis)) {
        valid =
            conditional_ports
                ? parseConditionalAnnexCommaListRule(port_list, port_item,
                                                     TK::CloseParenthesis)
                : parseAssertionPortListRule(closeKw == TK::EndPropertyKeyword);
      }
      if (!valid || !at(TK::CloseParenthesis)) {
        return false;
      }
      consumeInto(line_);
      skip_directives();
    }
    if (!at(TK::Semicolon)) {
      return false;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // property_spec ::= [ clocking_event ]
  //   [ disable iff '(' expression_or_dist ')' ] property_expr.
  [[nodiscard]] auto parsePropertySpecRule() -> bool {
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (at(TK::At) && !consumeAnnexRule("clocking_event", line_)) {
      return false;
    }
    skip_directives();
    if (at(TK::DisableKeyword)) {
      consumeInto(line_);
      skip_directives();
      if (!at(TK::IffKeyword)) {
        return false;
      }
      consumeInto(line_);
      skip_directives();
      if (!consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                 "expression_or_dist", line_)) {
        return false;
      }
      skip_directives();
    }
    return consumeAnnexRule("property_expr", line_, TK::Semicolon);
  }

  // assertion_variable_declaration ::= var_data_type
  //   list_of_variable_decl_assignments ';'. The optional implicit type is
  // available only after 'var'; an identifier immediately followed by the
  // list boundary is therefore the first assignment name.
  [[nodiscard]] auto parseAssertionVariableDeclarationRule() -> bool {
    const bool var = at(TK::VarKeyword);
    if (var) {
      consumeInto(line_);
    }
    parseGrammarChildDirectiveLines();
    const bool implicit_type =
        var && implicitIdentifierBefore({TK::Semicolon, TK::Equals, TK::Comma});
    if (!implicit_type &&
        !consumeAnnexRule(var ? "data_type_or_implicit" : "data_type", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    const bool conditional_members = hasConditionalListMember(pos_);
    if (!(hasAnnexListInterruption(pos_, conditional_members)
              ? consumeAnnexRule("list_of_variable_decl_assignments", line_,
                                 TK::Semicolon)
              : parseVariableAssignmentListRule(conditional_members))) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::Semicolon)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // Annex A gives property and sequence declarations a header, repeated local
  // declarations, and one final expression. A type prefix followed by a
  // declaration identifier enters the local declaration rule; the remaining
  // body enters property_spec or sequence_expr. Conditional branches retain
  // both body alternatives until their joined grammar state resolves them.
  auto parseAnnexWholeBlock(TK closeKw, std::string_view declarationRule)
      -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    const bool conditional_ports =
        at(TK::Identifier, 1) && at(TK::OpenParenthesis, 2) &&
        hasConditionalListMember(pos_ + 3, TK::CloseParenthesis);
    const bool direct_header =
        !hasAnnexHeaderInterruption(pos_, conditional_ports);
    bool complete = false;
    if (direct_header) {
      complete =
          parseAssertionDeclarationHeaderRule(closeKw, conditional_ports);
    } else {
      beginGrammar({declarationRule});
      consumeGrammarHeader(closeKw, {declarationRule});
      const AnnexState header = endGrammar(false);
      complete = !header.failed && !header.interrupted;
    }
    const std::string_view expression_rule =
        closeKw == TK::EndPropertyKeyword ? "property_spec" : "sequence_expr";
    const std::vector<std::string_view> body_rules = {
        "assertion_variable_declaration", expression_rule};
    if (complete) {
      ++indent_level_;
      while (true) {
        while (isCompilerDirective(peek()) &&
               !isConditionalStartDirective(peek()) &&
               !isConditionalBoundaryDirective(peek())) {
          addLine();
          parseDirectiveLine();
        }
        const size_t type_offset =
            at(TK::UnitSystemName) && at(TK::DoubleColon, 1) ? 2 : 0;
        const auto after_type = afterUserTypePrefix(type_offset);
        if (!(at(TK::VarKeyword) ||
              (annexCanStart("data_type", peek().kind) && !at(TK::Identifier) &&
               !at(TK::UnitSystemName)) ||
              (after_type && at(TK::Identifier, *after_type)))) {
          break;
        }
        if (!parseAssertionVariableDeclarationRule()) {
          complete = false;
          break;
        }
        addLine();
      }
    }
    const bool ambiguous_body = isConditionalStartDirective(peek());
    if (complete && !ambiguous_body) {
      bool conditional_body = false;
      if (closeKw == TK::EndPropertyKeyword) {
        for (size_t i = pos_; i < tokens_.size(); ++i) {
          if (isConditionalStartDirective(tokens_[i])) {
            conditional_body = true;
            break;
          }
          if (tokens_[i].kind == closeKw || tokens_[i].kind == TK::EndOfFile) {
            break;
          }
        }
      }
      complete =
          (closeKw == TK::EndPropertyKeyword && !conditional_body
               ? parsePropertySpecRule()
               : consumeAnnexRule(expression_rule, line_, TK::Semicolon)) &&
          (at(TK::Semicolon) || at(closeKw));
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
    }
    const bool body_started = complete;
    if (complete) {
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
      if (kind == TK::Semicolon) {
        addLine();
      }
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

  auto parseAnnexItem(const std::vector<std::string_view>& rules,
                      bool stop_at_complete_semicolon = false,
                      bool keep_completed_line_open = false) -> AnnexState {
    beginGrammar(rules);
    parseGrammarLeaf(false, {}, stop_at_complete_semicolon,
                     keep_completed_line_open);
    return endGrammar();
  }

  // Some parent productions append ';' to a child declaration. Keep the
  // child's final line open, then consume the parent's required terminal.
  auto parseAnnexSemicolonItem(std::string_view child_rule) -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({child_rule});
    parseGrammarLeaf(false, {}, false, true);
    const AnnexState child = endGrammar();
    if (child.failed || child.interrupted || !child.complete()) {
      return;
    }
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A parent semicolon");
      recoverMalformedItem(saved);
      return;
    }
    consumeInto(line_);
    addLine();
  }

  // interface_port_declaration ::= interface_identifier '.'
  // modport_identifier list_of_interface_identifiers. The qualified prefix
  // distinguishes this port declaration from a user-typed data declaration.
  auto parseQualifiedInterfacePortDeclarationRule() -> bool {
    if (!at(TK::Identifier) || !at(TK::Dot, 1) || !at(TK::Identifier, 2) ||
        !at(TK::Identifier, 3)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = consumeAnnexRule("interface_identifier", line_);
    parseGrammarChildDirectiveLines();
    if (valid && at(TK::Dot)) {
      consumeInto(line_);
    } else {
      valid = false;
    }
    parseGrammarChildDirectiveLines();
    if (valid) {
      valid = consumeAnnexRule("modport_identifier", line_);
    }
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!valid) {
        break;
      }
      parseGrammarChildDirectiveLines();
      valid = consumeAnnexRule("interface_identifier", line_);
      parseGrammarChildDirectiveLines();
      while (valid && at(TK::OpenBracket)) {
        valid = consumeAnnexRule("unpacked_dimension", line_);
        parseGrammarChildDirectiveLines();
      }
      if (!valid || !at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A interface port declaration");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // module_item, interface_item, and program_item append ';' to the shared
  // port_declaration production. Its leading keyword selects the Annex A
  // declaration child while tokens enter the output line.
  auto parsePortDeclarationRule() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    std::string_view declaration;
    switch (peek().kind) {
      case TK::InputKeyword:
        declaration = "input_declaration";
        break;
      case TK::OutputKeyword:
        declaration = "output_declaration";
        break;
      case TK::InOutKeyword:
        declaration = "inout_declaration";
        break;
      case TK::RefKeyword:
        declaration = "ref_declaration";
        break;
      default:
        recordGrammarFallback("invalid Annex A port declaration start");
        recoverMalformedLeaf(saved);
        return;
    }
    const bool directional = at(TK::InputKeyword) || at(TK::OutputKeyword);
    const bool explicit_net =
        directional && (annexCanStart("net_type", peek(1).kind) ||
                        at(TK::InterconnectKeyword, 1));
    const bool conditional_members = hasConditionalListMember(pos_);
    if (!hasAnnexListInterruption(pos_, conditional_members)) {
      const bool inout = at(TK::InOutKeyword);
      const bool output_variable = at(TK::OutputKeyword);
      consumeInto(line_);
      // The type can be implicit. Once an identifier and its dimensions
      // reach a list separator, that identifier begins the next production.
      // This also resolves net_port_type's nettype_identifier alternative.
      const auto identifier_ends_member = [&] {
        if (!at(TK::Identifier)) {
          return false;
        }
        size_t next = pos_ + 1;
        while (next < tokens_.size() && tokens_[next].kind == TK::OpenBracket) {
          int depth = 0;
          do {  // NOLINT(cppcoreguidelines-avoid-do-while)
            if (tokens_[next].kind == TK::OpenBracket) {
              ++depth;
            }
            if (tokens_[next].kind == TK::CloseBracket) {
              --depth;
            }
            ++next;
          } while (depth > 0 && next < tokens_.size());
          if (depth != 0) {
            return false;
          }
        }
        return next < tokens_.size() &&
               (tokens_[next].kind == TK::Semicolon ||
                tokens_[next].kind == TK::Comma ||
                (output_variable && tokens_[next].kind == TK::Equals));
      };
      const bool net = inout || explicit_net ||
                       (directional && !at(TK::VarKeyword) &&
                        (identifier_ends_member() ||
                         !annexCanStart("data_type", peek().kind)));
      const bool empty_net_type = net && identifier_ends_member();
      const bool valid =
          (empty_net_type ||
           consumeAnnexRule(net ? "net_port_type" : "variable_port_type", line_,
                            std::nullopt, identifier_ends_member)) &&
          parsePortIdentifierDimensionListRule(
              net               ? "list_of_port_identifiers"
              : output_variable ? "list_of_variable_port_identifiers"
                                : "list_of_variable_identifiers",
              net || output_variable ? "port_identifier"
                                     : "variable_identifier",
              net ? "unpacked_dimension" : "variable_dimension",
              output_variable && !net ? std::string_view{"constant_expression"}
                                      : std::string_view{},
              conditional_members);
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A port declaration");
        recoverMalformedLeaf(saved);
        return;
      }
      consumeInto(line_);
      addLine();
      return;
    }
    if (!consumeAnnexRule(declaration, line_, TK::Semicolon) ||
        !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A port declaration");
      recoverMalformedLeaf(saved);
      return;
    }
    consumeInto(line_);
    addLine();
  }

  // constraint_set ::= constraint_expression |
  //                    '{' { constraint_expression } '}'. The braced form
  // enters the child production for each member, without holding a chart
  // across an arbitrarily large constraint body.
  auto parseConstraintSetRule() -> bool {
    if (at(TK::EndOfFile) ||
        (stop_at_conditional_boundary_ &&
         isConditionalBoundaryDirective(peek())) ||
        std::ranges::any_of(block_stack_, [&](const BlockFrame& frame) {
          return matchesBlockClose(frame.close_kind, peek().kind);
        })) {
      recordGrammarFallback("missing Annex A constraint set");
      return false;
    }
    if (at(TK::OpenBrace)) {
      consumeInto(line_);
      addLine();
      parseDelimitedBody(TK::CloseBrace, "constraint_expression");
      return true;
    }
    parseIndentedStatement({"constraint_expression"});
    return true;
  }

  // constraint_block_item ::= solve solve_before_list before
  //                           solve_before_list ';' | constraint_expression.
  // solve_before_list ::= constraint_primary { ',' constraint_primary }.
  [[nodiscard]] auto parseSolveBeforeListRule(TK terminator) -> bool {
    const bool conditional_members = hasConditionalListMember(pos_, terminator);
    if (conditional_members ||
        hasAnnexListInterruption(pos_, conditional_members, terminator)) {
      return consumeAnnexRule("solve_before_list", line_, terminator);
    }
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("constraint_primary", line_, TK::Comma,
                            [&] { return at(terminator); })) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  auto parseConstraintBlockItemRule() -> bool {
    if (!at(TK::SolveKeyword)) {
      return parseConstraintExpressionRule();
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    if (!parseSolveBeforeListRule(TK::BeforeKeyword) ||
        !at(TK::BeforeKeyword)) {
      recordGrammarFallback("invalid Annex A solve before constraint");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    if (!parseSolveBeforeListRule(TK::Semicolon) || !at(TK::Semicolon)) {
      recordGrammarFallback("incomplete Annex A solve before constraint");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // Conditional compilation can split a keyword from the rest of its
  // production. Retain the live grammar continuation for that case.
  auto parseConditionalConstraintExpressionRule() -> bool {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"constraint_expression"});
    while (!at(TK::EndOfFile) &&
           !grammar_scopes_.back().hasActiveRule("constraint_set") &&
           !(grammar_scopes_.back().complete() &&
             !grammar_scopes_.back().accepts(peek().kind))) {
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
      if (!grammar_scopes_.back().accepts(peek().kind)) {
        break;
      }
      consumeInto(line_);
    }
    const AnnexState prefix = endGrammar(false);
    if (prefix.failed || prefix.interrupted ||
        (!prefix.complete() && !prefix.hasActiveRule("constraint_set"))) {
      recordGrammarFallback("invalid Annex A constraint expression");
      recoverMalformedItem(saved);
      return true;
    }
    if (!prefix.hasActiveRule("constraint_set")) {
      addLine();
      return true;
    }
    addLine();
    if (!parseConstraintSetRule()) {
      recoverMalformedItem(saved);
    }
    return true;
  }

  // Shared by loop_statement and constraint_expression after 'foreach':
  // '(' ps_or_hierarchical_array_identifier '[' loop_variables ']' ')'.
  [[nodiscard]] auto parseForeachHeaderRule() -> bool {
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    if (!consumeAnnexRule("ps_or_hierarchical_array_identifier", line_,
                          TK::OpenBracket)) {
      return false;
    }
    skip_directives();
    if (!at(TK::OpenBracket)) {
      return false;
    }
    consumeInto(line_);
    if (!at(TK::CloseBracket) &&
        !consumeAnnexRule("loop_variables", line_, TK::CloseBracket)) {
      return false;
    }
    skip_directives();
    if (!at(TK::CloseBracket)) {
      return false;
    }
    consumeInto(line_);
    skip_directives();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // constraint_expression chooses its Annex A alternative while reading the
  // source, then calls the corresponding child production.
  // range_list ::= value_range { ',' value_range }.
  [[nodiscard]] auto parseRangeListRule(TK terminator) -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("value_range", line_, TK::Comma,
                            [&] { return at(terminator); })) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  auto parseConstraintExpressionRule() -> bool {
    const auto skip_directives = [&] {
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    };
    if ((at(TK::IfKeyword) || at(TK::ForeachKeyword) || at(TK::UniqueKeyword) ||
         at(TK::SoftKeyword) || at(TK::DisableKeyword)) &&
        isConditionalStartDirective(peek(1))) {
      return parseConditionalConstraintExpressionRule();
    }
    if (at(TK::ForeachKeyword) && !isConditionalStartDirective(peek(1))) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);
      if (!parseForeachHeaderRule()) {
        recordGrammarFallback("incomplete Annex A constraint foreach header");
        recoverMalformedItem(saved);
        return true;
      }
      addLine();
      if (!parseConstraintSetRule()) {
        recoverMalformedItem(saved);
      }
      return true;
    }
    if (at(TK::DisableKeyword) &&
        at(TK::SoftKeyword, afterOrdinaryDirectives(1))) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);
      skip_directives();
      consumeInto(line_);
      skip_directives();
      const bool primary = consumeAnnexRule("constraint_primary", line_);
      skip_directives();
      if (!primary || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A disable soft constraint");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    if (at(TK::UniqueKeyword) && !isConditionalStartDirective(peek(1))) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
      if (!at(TK::OpenBrace)) {
        recordGrammarFallback("invalid Annex A uniqueness constraint");
        recoverMalformedItem(saved);
        return true;
      }
      const bool conditional_members =
          hasConditionalListMember(pos_ + 1, TK::CloseBrace);
      const bool interrupted =
          hasAnnexListInterruption(pos_ + 1, conditional_members,
                                   TK::CloseBrace) ||
          conditional_members;
      bool valid = true;
      if (interrupted) {
        valid = consumeAnnexDelimited(TK::OpenBrace, TK::CloseBrace,
                                      "range_list", line_);
      } else {
        consumeInto(line_);
        valid = parseRangeListRule(TK::CloseBrace) && at(TK::CloseBrace);
        if (valid) {
          consumeInto(line_);
        }
      }
      skip_directives();
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("incomplete Annex A uniqueness constraint");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      return true;
    }
    if (at(TK::IfKeyword) && !isConditionalStartDirective(peek(1))) {
      const LeafCheckpoint saved = leafCheckpoint();
      consumeInto(line_);
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
      if (!at(TK::OpenParenthesis)) {
        recordGrammarFallback("invalid Annex A constraint if condition");
        recoverMalformedItem(saved);
        return true;
      }
      const bool condition = consumeAnnexDelimited(
          TK::OpenParenthesis, TK::CloseParenthesis, "expression", line_);
      if (!condition || line_.tokens.empty() ||
          line_.tokens.back().kind != TK::CloseParenthesis) {
        recordGrammarFallback("incomplete Annex A constraint if condition");
        recoverMalformedItem(saved);
        return true;
      }
      addLine();
      if (!parseConstraintSetRule()) {
        recoverMalformedItem(saved);
        return true;
      }
      if (at(TK::ElseKeyword, afterOrdinaryDirectives(0))) {
        skip_directives();
        consumeInto(line_);
        addLine();
        if (!parseConstraintSetRule()) {
          recoverMalformedItem(saved);
        }
      }
      return true;
    }
    if (!annexCanStart("constraint_expression", peek().kind)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const bool soft = at(TK::SoftKeyword);
    if (soft) {
      consumeInto(line_);
      skip_directives();
    }
    if (!consumeAnnexRule("expression", line_, TK::MinusArrow)) {
      recordGrammarFallback("invalid Annex A constraint expression");
      recoverMalformedItem(saved);
      return true;
    }
    skip_directives();
    if (!soft && at(TK::MinusArrow)) {
      consumeInto(line_);
      addLine();
      if (!parseConstraintSetRule()) {
        recoverMalformedItem(saved);
      }
      return true;
    }
    if (at(TK::DistKeyword)) {
      consumeInto(line_);
      skip_directives();
      if (!at(TK::OpenBrace)) {
        recordGrammarFallback("invalid Annex A distribution constraint");
        recoverMalformedItem(saved);
        return true;
      }
      if (!consumeAnnexDelimited(TK::OpenBrace, TK::CloseBrace, "dist_list",
                                 line_)) {
        recoverMalformedItem(saved);
        return true;
      }
    }
    skip_directives();
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A constraint semicolon");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // class_constraint ::= constraint_prototype | constraint_declaration.
  // Both unqualified forms share the prefix through constraint_identifier;
  // the following Annex terminal selects ';' or constraint_block.
  [[nodiscard]] auto parseClassConstraintHeaderRule() -> std::optional<bool> {
    if (at(TK::StaticKeyword)) {
      consumeInto(line_);
    }
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if (!at(TK::ConstraintKeyword)) {
      return std::nullopt;
    }
    consumeInto(line_);
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if ((at(TK::Colon) && !consumeAnnexRule("dynamic_override_specifiers",
                                            line_, TK::Identifier)) ||
        !consumeAnnexRule("constraint_identifier", line_)) {
      return std::nullopt;
    }
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if (at(TK::Semicolon)) {
      consumeInto(line_);
      addLine();
      return false;
    }
    if (!at(TK::OpenBrace)) {
      return std::nullopt;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // extern_constraint_declaration ::= [static] constraint
  //   [dynamic_override_specifiers] class_scope constraint_identifier
  //   constraint_block. A class_scope can extend through another '::'; the
  // identifier followed by the block brace belongs to constraint_identifier.
  [[nodiscard]] auto parseExternConstraintHeaderRule() -> bool {
    if (at(TK::StaticKeyword)) {
      consumeInto(line_);
    }
    while (afterOrdinaryDirectives(0) > 0) {
      addLine();
      parseDirectiveLine();
    }
    if (!at(TK::ConstraintKeyword)) {
      return false;
    }
    consumeInto(line_);
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if (at(TK::Colon) && !consumeAnnexRule("dynamic_override_specifiers", line_,
                                           TK::Identifier)) {
      return false;
    }
    beginGrammar({"class_scope"});
    while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
                                   isConditionalBoundaryDirective(peek()))) {
      const auto& scope = grammar_scopes_.back();
      if (scope.complete() && at(TK::Identifier)) {
        size_t next = pos_ + 1;
        while (next < tokens_.size() && isCompilerDirective(tokens_[next]) &&
               !isConditionalStartDirective(tokens_[next])) {
          ++next;
        }
        if (next < tokens_.size() && tokens_[next].kind == TK::OpenBrace) {
          break;
        }
      }
      if (scope.complete() && !scope.accepts(peek().kind)) {
        break;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (!scope.accepts(peek().kind)) {
        break;
      }
      consumeInto(line_);
    }
    const AnnexState scope = endGrammar(false);
    if (scope.failed || scope.interrupted || !scope.complete() ||
        !consumeAnnexRule("constraint_identifier", line_)) {
      return false;
    }
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if (!at(TK::OpenBrace)) {
      return false;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  [[nodiscard]] auto conditionalInConstraintHeader() const -> bool {
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const Token token = tokens_[i];
      if (token.kind == TK::OpenBrace || token.kind == TK::Semicolon ||
          token.kind == TK::EndOfFile) {
        return false;
      }
      if (isConditionalStartDirective(token)) {
        return true;
      }
    }
    return false;
  }

  auto parseConstraintBlock(std::vector<std::string_view> roots = {
                                "constraint_declaration",
                                "extern_constraint_declaration"}) -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    bool opened = false;
    bool invalid = false;
    if (roots.size() == 1 && roots.front() == "class_constraint" &&
        !conditionalInConstraintHeader()) {
      const auto header = parseClassConstraintHeaderRule();
      if (!header) {
        invalid = true;
      } else if (!*header) {
        return;
      } else {
        opened = true;
      }
    } else if (roots.size() == 1 &&
               roots.front() == "extern_constraint_declaration" &&
               !conditionalInConstraintHeader()) {
      opened = parseExternConstraintHeaderRule();
      invalid = !opened;
    } else {
      beginGrammar(roots);
      while (!at(TK::EndOfFile) && !(stop_at_conditional_boundary_ &&
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
        if (!grammar_scopes_.back().accepts(peek().kind)) {
          break;
        }
        consumeInto(line_);
        if (grammar_scopes_.back().completed("extern_constraint_declaration") ||
            grammar_scopes_.back().completed("constraint_prototype")) {
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
      invalid = header.failed || header.interrupted;
    }
    if (!opened || invalid) {
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
      if (indent_level_ > 0) {
        --indent_level_;
      }
    }
  }

  auto parseDesignStatementRule() -> bool {
    if (!at(TK::DesignKeyword)) {
      return false;
    }
    if (hasAnnexListInterruption(pos_, false)) {
      const AnnexState item = parseAnnexItem({"design_statement"});
      if (item.complete()) {
        block_stack_.back().statement_phase = true;
      }
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // design
    parseGrammarChildDirectiveLines();
    bool valid = true;
    while (valid && at(TK::Identifier)) {
      if (at(TK::Dot, 1)) {
        valid = consumeAnnexRule("library_identifier", line_);
        if (!valid) {
          break;
        }
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
      }
      valid = consumeAnnexRule("cell_identifier", line_);
      parseGrammarChildDirectiveLines();
    }
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A design statement");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    block_stack_.back().statement_phase = true;
    return true;
  }

  auto parseConfigRuleStatementRule() -> bool {
    std::string_view clause;
    switch (peek().kind) {
      case TK::DefaultKeyword:
        clause = "default_clause";
        break;
      case TK::InstanceKeyword:
        clause = "inst_clause";
        break;
      case TK::CellKeyword:
        clause = "cell_clause";
        break;
      default:
        return false;
    }
    if (hasAnnexListInterruption(pos_, false)) {
      static_cast<void>(parseAnnexItem({"config_rule_statement"}));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    if (!consumeAnnexRule(clause, line_)) {
      recordGrammarFallback("invalid Annex A config selector");
      recoverMalformedItem(saved);
      return true;
    }
    parseGrammarChildDirectiveLines();
    const bool liblist = at(TK::LibListKeyword);
    if (!liblist && (clause == "default_clause" || !at(TK::UseKeyword))) {
      recordGrammarFallback("missing Annex A config rule clause");
      recoverMalformedItem(saved);
      return true;
    }
    const bool valid =
        consumeAnnexRule(liblist ? "liblist_clause" : "use_clause", line_);
    parseGrammarChildDirectiveLines();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A config rule clause");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  auto parseConfigBlock() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    bool interrupted_header = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        interrupted_header = true;
        break;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    if (interrupted_header) {
      beginGrammar({"config_declaration"});
      consumeGrammarHeader(TK::EndConfigKeyword, {"config_declaration"});
      static_cast<void>(endGrammar(false));
    } else {
      consumeInto(line_);  // config
      if (!consumeAnnexRule("config_identifier", line_) || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A config header");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      addLine();
    }
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

  auto parsePrimitiveBlock() -> void {
    bool interrupted_header = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token)) ||
          (token.kind == TK::OpenParenthesis && i + 2 < tokens_.size() &&
           tokens_[i + 1].kind == TK::Dot && tokens_[i + 2].kind == TK::Star)) {
        interrupted_header = true;
        break;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    bool nonansi = false;
    bool ansi = false;
    if (interrupted_header) {
      beginGrammar({"udp_declaration"});
      consumeGrammarHeader(TK::EndPrimitiveKeyword, {},
                           {"udp_nonansi_declaration", "udp_ansi_declaration",
                            "udp_declaration"});
      const AnnexState header = endGrammar(false);
      if (header.complete()) {
        return;  // extern declaration has no body
      }
      nonansi = header.completedFrom("udp_nonansi_declaration", 0);
      ansi = header.completedFrom("udp_ansi_declaration", 0);
    } else {
      const LeafCheckpoint saved = leafCheckpoint();
      const bool external = at(TK::ExternKeyword);
      if (external) {
        consumeInto(line_);
      }
      if (!at(TK::PrimitiveKeyword)) {
        recordGrammarFallback("invalid Annex A primitive keyword");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      if (!consumeAnnexRule("udp_identifier", line_) ||
          !at(TK::OpenParenthesis)) {
        recordGrammarFallback("invalid Annex A UDP identifier");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      nonansi = at(TK::Identifier);
      ansi = at(TK::OutputKeyword) || at(TK::OpenParenthesis);
      bool valid = false;
      if (nonansi) {
        valid = consumeAnnexRule("output_port_identifier", line_, TK::Comma);
        if (valid && at(TK::Comma)) {
          consumeInto(line_);
          valid = consumeAnnexRule("input_port_identifier", line_, TK::Comma);
        } else {
          valid = false;
        }
        while (valid && at(TK::Comma)) {
          consumeInto(line_);
          valid = consumeAnnexRule("input_port_identifier", line_, TK::Comma);
        }
      } else if (ansi) {
        valid = parseUdpOutputDeclarationRule(true);
        if (valid && at(TK::Comma)) {
          consumeInto(line_);
        } else {
          valid = false;
        }
        while (valid) {
          valid = parseUdpInputDeclarationRule(true);
          if (!valid || !at(TK::Comma)) {
            break;
          }
          consumeInto(line_);
        }
      }
      if (!valid || !at(TK::CloseParenthesis)) {
        recordGrammarFallback("invalid Annex A UDP port list");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      if (!at(TK::Semicolon)) {
        recordGrammarFallback("missing Annex A UDP header semicolon");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      addLine();
      if (external) {
        return;
      }
    }
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
        (at(TK::InputKeyword) || at(TK::OutputKeyword) || at(TK::RegKeyword))) {
      if (parseUdpPortDeclarationRule()) {
        auto& udp = block_stack_.back();
        udp.udp_port_on_all_paths = true;
        udp.udp_port_on_any_path = true;
      }
      return;
    }
    if (before_table && !body.udp_initial_seen && at(TK::InitialKeyword)) {
      block_stack_.back().udp_initial_seen = parseUdpInitialStatementRule();
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
        if (indent_level_ > 0) {
          --indent_level_;
        }
      }
      block_stack_.back().statement_phase = table_closed;
      return;
    }
    static_cast<void>(parseAnnexItem(grammarRoots()));
  }

  [[nodiscard]] auto udpSymbolMatches(std::string_view rule) const -> bool {
    AnnexState symbol({rule});
    symbol.advance(peek());
    return symbol.complete();
  }

  // seq_input_list ::= level_input_list | edge_input_list. Keep both Annex A
  // children live until ':', which also identifies the combinational form.
  [[nodiscard]] auto parseUdpInputListRule(bool& level_input) -> bool {
    beginGrammar({"level_input_list", "edge_input_list"});
    while (!at(TK::Colon) && !at(TK::EndOfFile) && !at(TK::Semicolon) &&
           !at(TK::EndTableKeyword) && !at(TK::EndPrimitiveKeyword)) {
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      } else {
        if (!grammar_scopes_.back().accepts(peek().kind)) {
          break;
        }
        consumeInto(line_);
      }
    }
    const AnnexState input = endGrammar(false);
    level_input = input.completed("level_input_list");
    return !input.failed && !input.interrupted && input.complete();
  }

  auto parseUdpTableEntryRule() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    bool interrupted = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        interrupted = true;
        break;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndTableKeyword ||
          token.kind == TK::EndPrimitiveKeyword ||
          token.kind == TK::EndOfFile) {
        break;
      }
    }
    if (interrupted) {
      const AnnexState entry = parseAnnexItem(grammarRoots());
      auto& table = block_stack_.back();
      table.udp_combinational |= entry.completed("combinational_entry");
      table.udp_sequential |= entry.completed("sequential_entry");
      table.udp_has_entry |= entry.complete();
      return;
    }
    auto& table = block_stack_.back();
    bool level_input = false;
    bool valid = parseUdpInputListRule(level_input) && at(TK::Colon);
    if (valid) {
      consumeInto(line_);
    }
    bool output_symbol = false;
    if (valid) {
      output_symbol = udpSymbolMatches("@lexer_output_symbol");
      valid = consumeAnnexRule("current_state", line_);
    }
    const bool sequential = valid && at(TK::Colon);
    if (valid) {
      valid =
          sequential ? true : at(TK::Semicolon) && level_input && output_symbol;
    }
    if (valid && ((sequential && table.udp_combinational) ||
                  (!sequential && table.udp_sequential))) {
      recordGrammarFallback("mixed Annex A UDP table entry forms");
      recoverMalformedLeaf(saved);
      return;
    }
    if (valid && sequential && at(TK::Colon)) {
      consumeInto(line_);
      valid = consumeAnnexRule("next_state", line_, TK::Semicolon);
    }
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A UDP table entry");
      recoverMalformedLeaf(saved);
      return;
    }
    consumeInto(line_);
    table.udp_sequential |= sequential;
    table.udp_combinational |= !sequential;
    table.udp_has_entry = true;
    addLine();
  }

  // list_of_udp_port_identifiers ::= port_identifier
  // { ',' port_identifier }.
  [[nodiscard]] auto parseUdpPortIdentifierListRule(bool header = false)
      -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("port_identifier", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      if (header) {
        size_t next = 1;
        while (isCompilerDirective(peek(next))) {
          ++next;
        }
        if (at(TK::InputKeyword, next) ||
            (at(TK::OpenParenthesis, next) && at(TK::Star, next + 1))) {
          break;
        }
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // udp_output_declaration ::= { attribute_instance } output [ reg ]
  // port_identifier [ '=' constant_expression (only after reg) ].
  [[nodiscard]] auto parseUdpOutputDeclarationRule(bool header) -> bool {
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (!at(TK::OutputKeyword)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    const bool registered = at(TK::RegKeyword);
    if (registered) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
    }
    if (!consumeAnnexRule("port_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (registered && at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("constant_expression", line_,
                            header ? TK::Comma : TK::Semicolon,
                            [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    return true;
  }

  // udp_input_declaration ::= { attribute_instance } input
  // list_of_udp_port_identifiers.
  [[nodiscard]] auto parseUdpInputDeclarationRule(bool header) -> bool {
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (!at(TK::InputKeyword)) {
      return false;
    }
    consumeInto(line_);
    return parseUdpPortIdentifierListRule(header);
  }

  [[nodiscard]] auto parseUdpPortDeclarationRule() -> bool {
    if (!at(TK::OutputKeyword) && !at(TK::InputKeyword) &&
        !at(TK::RegKeyword)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = true;
    if (at(TK::OutputKeyword)) {
      valid = parseUdpOutputDeclarationRule(false);
    } else if (at(TK::InputKeyword)) {
      valid = parseUdpInputDeclarationRule(false);
    } else {
      consumeInto(line_);
      valid = consumeAnnexRule("variable_identifier", line_);
    }
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A UDP port declaration");
      recoverMalformedItem(saved);
      return false;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  [[nodiscard]] auto parseUdpInitialStatementRule() -> bool {
    if (!at(TK::InitialKeyword)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    if (!consumeAnnexRule("output_port_identifier", line_) || !at(TK::Equals)) {
      recordGrammarFallback("invalid Annex A UDP initial output");
      recoverMalformedItem(saved);
      return false;
    }
    consumeInto(line_);
    if (!consumeAnnexRule("init_val", line_, TK::Semicolon) ||
        !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A UDP initial value");
      recoverMalformedItem(saved);
      return false;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // package_declaration ::= {attribute_instance} package [lifetime]
  //                         package_identifier ';' ... endpackage.
  // The enclosing description rule has already consumed any attributes.
  [[nodiscard]] auto parsePackageHeaderRule() -> bool {
    consumeInto(line_);
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if ((at(TK::StaticKeyword) || at(TK::AutomaticKeyword)) &&
        !consumeAnnexRule("lifetime", line_)) {
      return false;
    }
    skip_directives();
    if (!consumeAnnexRule("package_identifier", line_)) {
      return false;
    }
    skip_directives();
    if (!at(TK::Semicolon)) {
      return false;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  [[nodiscard]] auto conditionalInPackageHeader() const -> bool {
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      if (tokens_[i].kind == TK::Semicolon ||
          tokens_[i].kind == TK::EndOfFile) {
        return false;
      }
      if (isConditionalStartDirective(tokens_[i])) {
        return true;
      }
    }
    return false;
  }

  auto recoverMalformedStructuralHeader(const LeafCheckpoint& saved, TK closeKw,
                                        bool external = false) -> void {
    if (external) {
      recoverMalformedLeaf(saved);
      return;
    }
    lines_.resize(saved.output_size);
    line_ = saved.line;
    preserved_source_end_ = saved.preserved_source_end;
    indent_level_ = saved.indent_level;
    pos_ = saved.pos;
    const auto after = findPairedEnd(saved.pos, closeKw);
    emitOpaque(saved.pos, after ? *after : findOuterBoundary(saved.pos));
  }

  // The ANSI header may omit list_of_port_declarations entirely. For that
  // production, parse each child directly and enter non_port_*_item.
  [[nodiscard]] auto parsePortlessStructuralHeaderRule(TK closeKw) -> bool {
    size_t identifier_offset = 1;
    if (at(TK::StaticKeyword, identifier_offset) ||
        at(TK::AutomaticKeyword, identifier_offset)) {
      ++identifier_offset;
    }
    if (!at(TK::Identifier, identifier_offset) ||
        !at(TK::Semicolon, identifier_offset + 1)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    std::string_view identifier_rule;
    switch (closeKw) {
      case TK::EndModuleKeyword:
        identifier_rule = "module_identifier";
        break;
      case TK::EndInterfaceKeyword:
        identifier_rule = "interface_identifier";
        break;
      case TK::EndProgramKeyword:
        identifier_rule = "program_identifier";
        break;
      default:
        return false;
    }
    consumeInto(line_);
    bool valid = true;
    if (at(TK::StaticKeyword) || at(TK::AutomaticKeyword)) {
      valid = consumeAnnexRule("lifetime", line_);
    }
    valid = valid && consumeAnnexRule(identifier_rule, line_);
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A structural header");
      recoverMalformedStructuralHeader(saved, closeKw);
      return true;
    }
    consumeInto(line_);
    addLine();
    const std::string_view body_rule =
        closeKw == TK::EndModuleKeyword      ? "non_port_module_item"
        : closeKw == TK::EndInterfaceKeyword ? "non_port_interface_item"
                                             : "non_port_program_item";
    parseDelimitedBody(closeKw, body_rule);
    return true;
  }

  // parameter_port_list has two alternatives. A comma continues the current
  // assignment list when the next tokens can form its identifier and optional
  // dimensions; otherwise it starts another parameter_port_declaration.
  [[nodiscard]] auto startsParameterPortDeclaration() const -> bool {
    if (!at(TK::Identifier)) {
      return true;
    }
    const auto next = afterBalancedDimensions(1);
    if (!next) {
      return true;
    }
    const size_t boundary = afterOrdinaryDirectives(*next);
    return at(TK::Identifier, boundary) || at(TK::DoubleColon, boundary) ||
           at(TK::Hash, boundary) || at(TK::Dot, boundary);
  }

  // parameter_port_declaration can select type_parameter_declaration when
  // its 'type' terminal is present. The enclosing list handles further type
  // assignments after commas, so this function emits its first child now.
  [[nodiscard]] auto parseTypeParameterPortDeclarationRule() -> bool {
    if (at(TK::ParameterKeyword) || at(TK::LocalParamKeyword)) {
      if (!at(TK::TypeKeyword, afterOrdinaryDirectives(1))) {
        return false;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
    }
    if (!at(TK::TypeKeyword)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (annexCanStart("forward_type", peek().kind) &&
        !consumeAnnexRule("forward_type", line_)) {
      return false;
    }
    return parseParameterAssignmentRule(true);
  }

  // The parameter/localparam alternatives and an explicit built-in data_type
  // have a distinct prefix. A user-defined type keeps the local declaration
  // chart because it shares an identifier start with a bare assignment.
  [[nodiscard]] auto parseDataParameterPortDeclarationRule() -> bool {
    const bool keyword = at(TK::ParameterKeyword) || at(TK::LocalParamKeyword);
    if (keyword) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (at(TK::TypeKeyword) && !at(TK::OpenParenthesis, 1)) {
        return false;
      }
      if (!(at(TK::Identifier) && !startsParameterPortDeclaration()) &&
          !consumeAnnexRule("data_type_or_implicit", line_)) {
        return false;
      }
    } else {
      if ((at(TK::Identifier) && !startsParameterPortDeclaration()) ||
          !annexCanStart("data_type", peek().kind) ||
          !consumeAnnexRule("data_type", line_)) {
        return false;
      }
    }
    return parseParameterAssignmentRule(false);
  }

  [[nodiscard]] auto parseParameterPortListRule() -> bool {
    if (!at(TK::Hash) || !at(TK::OpenParenthesis, 1)) {
      return false;
    }
    consumeInto(line_);
    consumeInto(line_);
    addLine();
    parseGrammarChildDirectiveLines();
    if (!at(TK::CloseParenthesis)) {
      bool bare_assignments = !startsParameterPortDeclaration();
      std::string_view assignment = "param_assignment";
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        parseGrammarChildDirectiveLines();
        const bool declaration =
            !bare_assignments && startsParameterPortDeclaration();
        const size_t type_start = afterOrdinaryDirectives(1);
        if (declaration) {
          assignment = (at(TK::TypeKeyword) && !at(TK::OpenParenthesis, 1)) ||
                               ((at(TK::ParameterKeyword) ||
                                 at(TK::LocalParamKeyword)) &&
                                at(TK::TypeKeyword, type_start) &&
                                !at(TK::OpenParenthesis,
                                    afterOrdinaryDirectives(type_start + 1)))
                           ? "type_assignment"
                           : "param_assignment";
        }
        const bool type_declaration =
            declaration &&
            ((at(TK::TypeKeyword) && !at(TK::OpenParenthesis, 1)) ||
             ((at(TK::ParameterKeyword) || at(TK::LocalParamKeyword)) &&
              at(TK::TypeKeyword, type_start) &&
              !at(TK::OpenParenthesis,
                  afterOrdinaryDirectives(type_start + 1))));
        const bool data_declaration =
            declaration &&
            ((at(TK::ParameterKeyword) || at(TK::LocalParamKeyword)) ||
             annexCanStart("data_type", peek().kind));
        const bool valid =
            type_declaration   ? parseTypeParameterPortDeclarationRule()
            : data_declaration ? parseDataParameterPortDeclarationRule()
            : declaration
                ? consumeAnnexRule("parameter_port_declaration", line_,
                                   TK::Comma,
                                   [&] { return at(TK::CloseParenthesis); })
                : parseParameterAssignmentRule(assignment == "type_assignment");
        if (!valid) {
          return false;
        }
        bare_assignments = false;
        parseGrammarChildDirectiveLines();
        if (!at(TK::Comma)) {
          break;
        }
        consumeInto(line_);
        addLine();
      } while (!at(TK::EndOfFile));
    }
    addLine();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // port ::= [ port_expression ] | '.' port_identifier '(' [ port_expression
  // ] ')'. The enclosing list has already selected its non-ANSI alternative.
  [[nodiscard]] auto parseNonAnsiPortMemberRule() -> bool {
    if (at(TK::Comma) || at(TK::CloseParenthesis)) {
      return true;
    }
    if (at(TK::Dot)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("port_identifier", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::OpenParenthesis)) {
        return false;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!at(TK::CloseParenthesis) &&
          !consumeAnnexRule("port_expression", line_, TK::CloseParenthesis)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::CloseParenthesis)) {
        return false;
      }
      consumeInto(line_);
      return true;
    }
    return consumeAnnexRule("port_expression", line_, TK::Comma,
                            [&] { return at(TK::CloseParenthesis); });
  }

  // list_of_ports and list_of_port_declarations can share a leading named
  // port or identifier. Keep both Annex A alternatives only until a member
  // resolves the list; subsequent members enter their child functions.
  [[nodiscard]] auto parseSharedStructuralPortListRule(bool& nonansi) -> bool {
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    addLine();
    bool ansi = true;
    nonansi = true;
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      parseGrammarChildDirectiveLines();
      const bool attributes = at(TK::OpenParenthesis) && at(TK::Star, 1);
      const bool qualified_interface = at(TK::Identifier) && at(TK::Dot, 1) &&
                                       at(TK::Identifier, 2) &&
                                       at(TK::Identifier, 3);
      if (attributes || qualified_interface) {
        if (!ansi) {
          return false;
        }
        nonansi = false;
      }
      if (!nonansi) {
        if (!parseAnsiPortMemberRule()) {
          return false;
        }
      } else if (!ansi) {
        if (!parseNonAnsiPortMemberRule()) {
          return false;
        }
      } else if (at(TK::Comma) || at(TK::CloseParenthesis)) {
        // port ::= [ port_expression ] has an empty alternative.
        ansi = false;
      } else {
        beginGrammar({"port", "ansi_port_declaration"});
        while (!at(TK::EndOfFile)) {
          const auto& grammar = grammar_scopes_.back();
          if (grammar.complete() &&
              (at(TK::Comma) || at(TK::CloseParenthesis))) {
            break;
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
          consumeInto(line_);
        }
        const AnnexState item = endGrammar(false);
        if (item.failed || item.interrupted) {
          return false;
        }
        nonansi &= item.completed("port");
        ansi &= item.completed("ansi_port_declaration");
        if (!nonansi && !ansi) {
          return false;
        }
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
      addLine();
    } while (!at(TK::EndOfFile));
    addLine();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  // interface_port_header selects the first ansi_port_declaration alternative.
  [[nodiscard]] auto parseInterfaceAnsiPortRule() -> bool {
    if (!at(TK::InterfaceKeyword) && !at(TK::Identifier)) {
      return false;
    }
    if (!consumeAnnexRule("interface_port_header", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("port_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule("unpacked_dimension", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("constant_expression", line_, TK::Comma,
                            [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    return true;
  }

  [[nodiscard]] auto ansiIdentifierEndsMember(size_t offset = 0) const -> bool {
    if (!at(TK::Identifier, offset)) {
      return false;
    }
    const auto next = afterBalancedDimensions(offset + 1);
    return next && (at(TK::Comma, *next) || at(TK::CloseParenthesis, *next) ||
                    at(TK::Equals, *next));
  }

  // The selected ansi_port_declaration alternative enters its header rule.
  // A net header can be empty. Stop it before the identifier that ends this
  // member, including when the identifier has unpacked dimensions.
  [[nodiscard]] auto parseTypedAnsiPortRule(bool variable) -> bool {
    const bool empty_header = ansiIdentifierEndsMember();
    if (!empty_header &&
        !consumeAnnexRule(variable ? "variable_port_header" : "net_port_header",
                          line_, std::nullopt,
                          [&] { return ansiIdentifierEndsMember(); })) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("port_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule(
              variable ? "variable_dimension" : "unpacked_dimension", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("constant_expression", line_, TK::Comma,
                            [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    return true;
  }

  // A user type can be a nettype, variable type, or interface identifier.
  // Keep those three header productions live only through their shared
  // prefix. The remaining port_identifier, dimensions and initializer enter
  // their own Annex A children in this same pass.
  [[nodiscard]] auto parseAmbiguousAnsiPortRule() -> bool {
    beginGrammar(
        {"net_port_header", "variable_port_header", "interface_port_header"});
    while (!at(TK::EndOfFile)) {
      const auto& header = grammar_scopes_.back();
      if (header.complete() && ansiIdentifierEndsMember()) {
        break;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
        continue;
      }
      if (header.failed || header.interrupted || !header.accepts(peek().kind)) {
        break;
      }
      consumeInto(line_);
    }
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted || !header.complete() ||
        !ansiIdentifierEndsMember()) {
      return false;
    }
    const bool variable = header.completed("variable_port_header");
    if (!variable && !header.completed("net_port_header") &&
        !header.completed("interface_port_header")) {
      return false;
    }
    if (!consumeAnnexRule("port_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule(
              variable ? "variable_dimension" : "unpacked_dimension", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("constant_expression", line_, TK::Comma,
                            [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    return true;
  }

  // { attribute_instance } ansi_port_declaration, after the enclosing list
  // has chosen its ANSI production.
  [[nodiscard]] auto parseAnsiPortMemberRule() -> bool {
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      skip_directives();
    }
    const bool named =
        at(TK::Dot) || ((at(TK::InputKeyword) || at(TK::OutputKeyword) ||
                         at(TK::InOutKeyword) || at(TK::RefKeyword)) &&
                        at(TK::Dot, 1));
    if (named) {
      if (!at(TK::Dot) && !consumeAnnexRule("port_direction", line_)) {
        return false;
      }
      if (!parseModportSimplePortRule()) {
        return false;
      }
    } else if (at(TK::InterfaceKeyword) ||
               (at(TK::Identifier) && at(TK::Dot, 1) && at(TK::Identifier, 2) &&
                at(TK::Identifier, 3))) {
      if (!parseInterfaceAnsiPortRule()) {
        return false;
      }
    } else {
      const size_t type_offset =
          at(TK::InputKeyword) || at(TK::OutputKeyword) ||
                  at(TK::InOutKeyword) || at(TK::RefKeyword)
              ? 1
              : 0;
      const bool variable_type =
          at(TK::VarKeyword, type_offset) ||
          (annexCanStart("data_type", peek(type_offset).kind) &&
           !at(TK::Identifier, type_offset) &&
           !at(TK::UnitSystemName, type_offset));
      if (variable_type || at(TK::InterconnectKeyword, type_offset) ||
          annexCanStart("net_type", peek(type_offset).kind) ||
          at(TK::SignedKeyword, type_offset) ||
          at(TK::UnsignedKeyword, type_offset) ||
          at(TK::OpenBracket, type_offset) ||
          ansiIdentifierEndsMember(type_offset)) {
        if (!parseTypedAnsiPortRule(variable_type)) {
          return false;
        }
      } else if (!parseAmbiguousAnsiPortRule()) {
        return false;
      }
    }
    skip_directives();
    return true;
  }

  // list_of_port_declarations ::= '(' [ { attribute_instance }
  // ansi_port_declaration { ',' { attribute_instance }
  // ansi_port_declaration } ] ')'.
  [[nodiscard]] auto parseAnsiStructuralPortListRule() -> bool {
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    addLine();
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseAnsiPortMemberRule()) {
        return false;
      }
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
      addLine();
    } while (!at(TK::EndOfFile));
    addLine();
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  [[nodiscard]] auto parseStructuralHeaderRule(TK closeKw,
                                               bool external = false) -> bool {
    // Conditional branches and unavailable macro expansions can change the
    // header production. They keep the existing interrupted chart path.
    int parens = 0;
    bool import_segment = false;
    for (size_t i = pos_ + (external ? 1 : 0); i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) ||
          isConditionalBoundaryDirective(token) ||
          token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        return false;
      }
      if (token.kind == TK::OpenParenthesis) {
        ++parens;
      }
      if (token.kind == TK::CloseParenthesis) {
        --parens;
      }
      if (token.kind == TK::OpenParenthesis && i + 2 < tokens_.size() &&
          tokens_[i + 1].kind == TK::Dot && tokens_[i + 2].kind == TK::Star) {
        return false;
      }
      if (parens == 0 && token.kind == TK::ImportKeyword) {
        import_segment = true;
      }
      if (parens == 0 && token.kind == TK::Semicolon) {
        if (!import_segment) {
          break;
        }
        import_segment = false;
      }
      if (token.kind == closeKw || token.kind == TK::EndOfFile) {
        return false;
      }
    }

    const LeafCheckpoint saved = leafCheckpoint();
    std::string_view identifier_rule;
    std::string_view body_rule;
    std::string_view non_port_body_rule;
    switch (closeKw) {
      case TK::EndModuleKeyword:
        identifier_rule = "module_identifier";
        body_rule = "module_item";
        non_port_body_rule = "non_port_module_item";
        break;
      case TK::EndInterfaceKeyword:
        identifier_rule = "interface_identifier";
        body_rule = "interface_item";
        non_port_body_rule = "non_port_interface_item";
        break;
      case TK::EndProgramKeyword:
        identifier_rule = "program_identifier";
        body_rule = "program_item";
        non_port_body_rule = "non_port_program_item";
        break;
      default:
        return false;
    }
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    if (external) {
      consumeInto(line_);  // extern
    }
    consumeInto(line_);  // module_keyword / interface / program
    skip_directives();
    if (at(TK::StaticKeyword) || at(TK::AutomaticKeyword)) {
      if (!consumeAnnexRule("lifetime", line_)) {
        recordGrammarFallback("invalid Annex A structural lifetime");
        recoverMalformedStructuralHeader(saved, closeKw, external);
        return true;
      }
    }
    skip_directives();
    if (!consumeAnnexRule(identifier_rule, line_)) {
      recordGrammarFallback("invalid Annex A structural identifier");
      recoverMalformedStructuralHeader(saved, closeKw, external);
      return true;
    }
    skip_directives();
    while (at(TK::ImportKeyword)) {
      if (!parseHeaderPackageImportRule()) {
        recordGrammarFallback("invalid Annex A header package import");
        recoverMalformedStructuralHeader(saved, closeKw, external);
        return true;
      }
      skip_directives();
    }
    if (at(TK::Hash)) {
      if (!parseParameterPortListRule()) {
        recordGrammarFallback("invalid Annex A parameter port list");
        recoverMalformedStructuralHeader(saved, closeKw, external);
        return true;
      }
      skip_directives();
    }
    if (at(TK::OpenParenthesis)) {
      const bool direct_ansi =
          at(TK::InputKeyword, 1) || at(TK::OutputKeyword, 1) ||
          at(TK::InOutKeyword, 1) || at(TK::RefKeyword, 1) ||
          at(TK::InterfaceKeyword, 1) ||
          (at(TK::OpenParenthesis, 1) && at(TK::Star, 2)) ||
          (annexCanStart("data_type", peek(1).kind) && !at(TK::Identifier, 1) &&
           !at(TK::UnitSystemName, 1));
      if (direct_ansi) {
        if (!parseAnsiStructuralPortListRule()) {
          recordGrammarFallback("invalid Annex A ANSI structural port list");
          recoverMalformedStructuralHeader(saved, closeKw, external);
          return true;
        }
        body_rule = non_port_body_rule;
      } else {
        bool nonansi = false;
        if (!parseSharedStructuralPortListRule(nonansi)) {
          recordGrammarFallback("invalid Annex A structural port list");
          recoverMalformedStructuralHeader(saved, closeKw, external);
          return true;
        }
        if (!nonansi) {
          body_rule = non_port_body_rule;
        }
      }
      skip_directives();
    } else {
      body_rule = non_port_body_rule;
    }
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A structural header semicolon");
      recoverMalformedStructuralHeader(saved, closeKw, external);
      return true;
    }
    consumeInto(line_);
    addLine();
    if (!external) {
      parseDelimitedBody(closeKw, body_rule);
    }
    return true;
  }

  auto parseStructuralBlock(TK closeKw) -> void {
    if (closeKw == TK::EndPackageKeyword && !conditionalInPackageHeader()) {
      const LeafCheckpoint saved = leafCheckpoint();
      if (!parsePackageHeaderRule()) {
        recordGrammarFallback("invalid Annex A package header");
        lines_.resize(saved.output_size);
        line_ = saved.line;
        preserved_source_end_ = saved.preserved_source_end;
        indent_level_ = saved.indent_level;
        pos_ = saved.pos;
        const auto after = findPairedEnd(pos_, closeKw);
        emitOpaque(pos_, after ? *after : findOuterBoundary(pos_));
        return;
      }
      parseDelimitedBody(closeKw, "package_item");
      return;
    }
    if (parsePortlessStructuralHeaderRule(closeKw)) {
      return;
    }
    if (parseStructuralHeaderRule(closeKw)) {
      return;
    }
    std::vector<std::string_view> roots;
    std::string_view body_rule;
    std::string_view declaration_rule;
    switch (closeKw) {
      case TK::EndModuleKeyword:
        roots = {"module_ansi_header", "module_nonansi_header",
                 "module_declaration"};
        declaration_rule = "module_declaration";
        body_rule = "module_item";
        break;
      case TK::EndInterfaceKeyword:
        roots = {"interface_ansi_header", "interface_nonansi_header",
                 "interface_declaration"};
        declaration_rule = "interface_declaration";
        body_rule = "interface_item";
        break;
      case TK::EndProgramKeyword:
        roots = {"program_ansi_header", "program_nonansi_header",
                 "program_declaration"};
        declaration_rule = "program_declaration";
        body_rule = "program_item";
        break;
      case TK::EndPackageKeyword:
        roots = {"package_declaration"};
        body_rule = "package_item";
        break;
      default:
        break;
    }
    if (!roots.empty()) {
      beginGrammar(roots);
    }
    if (closeKw == TK::EndPackageKeyword) {
      // package_declaration includes its body; the first grammar-accepted
      // semicolon separates its header from package_item repetitions.
      consumeGrammarHeader(closeKw, {"package_declaration"});
    } else {
      // The header chart ends the header, including any package imports. A
      // semicolon inside an import cannot be mistaken for the body boundary.
      while (!at(closeKw) && !at(TK::EndOfFile) &&
             !grammar_scopes_.back().complete() &&
             (declaration_rule.empty() ||
              !grammar_scopes_.back().consumedTerminalInRule(declaration_rule,
                                                             TK::Semicolon))) {
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
            if (kind == TK::Semicolon) {
              break;
            }
          }
          continue;
        }
        if (!grammar_scopes_.back().accepts(peek().kind)) {
          break;
        }
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
    const AnnexState header = endGrammar(false);
    if (!header.complete() &&
        (declaration_rule.empty() ||
         !header.consumedTerminalInRule(declaration_rule, TK::Semicolon)) &&
        !header.interrupted) {
      recordGrammarFallback("header outside Annex A declaration");
    }
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

  [[nodiscard]] auto parseTfHeaderPortListRule() -> bool {
    if (!at(TK::OpenParenthesis)) {
      return false;
    }
    consumeInto(line_);
    if (!at(TK::CloseParenthesis) && !parseTfPortListRule()) {
      return false;
    }
    if (!at(TK::CloseParenthesis)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  [[nodiscard]] auto parseTaskFunctionBlockRule(TK closeKw) -> bool {
    if (closeKw != TK::EndTaskKeyword && closeKw != TK::EndFunctionKeyword) {
      return false;
    }
    if (isConditionalStartDirective(peek(1)) ||
        peek(1).kind == TK::MacroUsage) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);  // task / function
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (at(TK::Colon) &&
        !consumeAnnexRule("dynamic_override_specifiers", line_)) {
      recordGrammarFallback("invalid Annex A task/function specifier");
      recoverMalformedItem(saved);
      return true;
    }
    skip_directives();
    if ((at(TK::StaticKeyword) || at(TK::AutomaticKeyword)) &&
        !consumeAnnexRule("lifetime", line_)) {
      recordGrammarFallback("invalid Annex A task/function lifetime");
      recoverMalformedItem(saved);
      return true;
    }
    skip_directives();
    const std::string_view body_rule = closeKw == TK::EndTaskKeyword
                                           ? "task_body_declaration"
                                           : "function_body_declaration";
    bool interrupted_header = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      if (isConditionalStartDirective(tokens_[i]) ||
          tokens_[i].kind == TK::MacroUsage) {
        interrupted_header = true;
        break;
      }
      if (tokens_[i].kind == TK::Semicolon ||
          tokens_[i].kind == TK::EndOfFile) {
        break;
      }
    }
    if (closeKw == TK::EndTaskKeyword && !interrupted_header &&
        at(TK::Identifier) &&
        (at(TK::Semicolon, 1) || at(TK::OpenParenthesis, 1))) {
      if (!consumeAnnexRule("task_identifier", line_)) {
        recordGrammarFallback("invalid Annex A task identifier");
        recoverMalformedItem(saved);
        return true;
      }
      const bool ports_in_header = at(TK::OpenParenthesis);
      if (ports_in_header && !parseTfHeaderPortListRule()) {
        recordGrammarFallback("invalid Annex A task port list");
        recoverMalformedItem(saved);
        return true;
      }
      if (!at(TK::Semicolon)) {
        recordGrammarFallback("missing Annex A task header semicolon");
        recoverMalformedItem(saved);
        return true;
      }
      consumeInto(line_);
      addLine();
      parseDelimitedBody(closeKw, {}, false, ports_in_header);
      return true;
    }
    if (closeKw == TK::EndFunctionKeyword && !interrupted_header) {
      const bool implicit_type =
          at(TK::Identifier) &&
          (at(TK::Semicolon, 1) || at(TK::OpenParenthesis, 1));
      const bool typed =
          !implicit_type &&
          (annexCanStart("function_data_type_or_implicit", peek().kind) &&
           !(at(TK::Identifier) && (at(TK::DoubleColon, 1) || at(TK::Dot, 1))));
      if (implicit_type || typed) {
        bool valid = implicit_type ||
                     consumeAnnexRule("function_data_type_or_implicit", line_);
        if (valid) {
          valid = consumeAnnexRule("function_identifier", line_);
        }
        const bool ports_in_header = at(TK::OpenParenthesis);
        if (valid && ports_in_header) {
          valid = parseTfHeaderPortListRule();
        }
        if (!valid || !at(TK::Semicolon)) {
          recordGrammarFallback("invalid Annex A function header");
          recoverMalformedItem(saved);
          return true;
        }
        consumeInto(line_);
        addLine();
        parseDelimitedBody(closeKw, {}, false, ports_in_header);
        return true;
      }
    }
    beginGrammar({body_rule});
    consumeGrammarHeader(closeKw, {body_rule});
    const AnnexState header = endGrammar(false);
    if (header.failed || header.interrupted ||
        !header.consumedTerminalInRule(body_rule, TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A task/function header");
      recoverMalformedItem(saved);
      return true;
    }
    const bool ports_in_header =
        header.hasActiveProductionContaining(body_rule, TK::OpenParenthesis);
    parseDelimitedBody(closeKw, {}, false, ports_in_header);
    return true;
  }

  [[nodiscard]] auto parseClassBlockRule(TK closeKw) -> bool {
    if (closeKw != TK::EndClassKeyword) {
      return false;
    }
    const bool interface_class =
        at(TK::InterfaceKeyword) && at(TK::ClassKeyword, 1);
    if (!interface_class && !at(TK::ClassKeyword) &&
        !(at(TK::VirtualKeyword) && at(TK::ClassKeyword, 1))) {
      return false;
    }
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        return false;
      }
      if (token.kind == TK::Semicolon || token.kind == TK::EndOfFile) {
        break;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    if (interface_class || at(TK::VirtualKeyword)) {
      consumeInto(line_);
    }
    consumeInto(line_);  // class
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    skip_directives();
    if (!interface_class && at(TK::Colon)) {
      if (!consumeAnnexRule("final_specifier", line_)) {
        recordGrammarFallback("invalid Annex A class final specifier");
        recoverMalformedItem(saved);
        return true;
      }
      skip_directives();
    }
    if (!consumeAnnexRule("class_identifier", line_)) {
      recordGrammarFallback("invalid Annex A class identifier");
      recoverMalformedItem(saved);
      return true;
    }
    skip_directives();
    if (at(TK::Hash)) {
      if (!parseParameterPortListRule()) {
        recordGrammarFallback("invalid Annex A class parameter list");
        recoverMalformedItem(saved);
        return true;
      }
      skip_directives();
    }
    if (at(TK::ExtendsKeyword)) {
      consumeInto(line_);
      skip_directives();
      const std::string_view parent_rule =
          interface_class ? "interface_class_type" : "class_type";
      if (!consumeAnnexRule(parent_rule, line_, TK::Comma)) {
        recordGrammarFallback("invalid Annex A class extends type");
        recoverMalformedItem(saved);
        return true;
      }
      if (interface_class) {
        while (at(TK::Comma)) {
          consumeInto(line_);
          if (!consumeAnnexRule("interface_class_type", line_, TK::Comma)) {
            recordGrammarFallback("invalid Annex A interface class parent");
            recoverMalformedItem(saved);
            return true;
          }
        }
      } else if (at(TK::OpenParenthesis)) {
        if (at(TK::CloseParenthesis, 1)) {
          consumeInto(line_);
          consumeInto(line_);
        } else if (at(TK::DefaultKeyword, 1) && at(TK::CloseParenthesis, 2)) {
          consumeInto(line_);
          consumeInto(line_);
          consumeInto(line_);
        } else if (!consumeAnnexDelimited(TK::OpenParenthesis,
                                          TK::CloseParenthesis,
                                          "list_of_arguments", line_)) {
          recoverMalformedItem(saved);
          return true;
        }
      }
      skip_directives();
    }
    if (!interface_class && at(TK::ImplementsKeyword)) {
      consumeInto(line_);
      bool valid = consumeAnnexRule("interface_class_type", line_, TK::Comma);
      while (valid && at(TK::Comma)) {
        consumeInto(line_);
        valid = consumeAnnexRule("interface_class_type", line_, TK::Comma);
      }
      if (!valid) {
        recordGrammarFallback("invalid Annex A class implements type");
        recoverMalformedItem(saved);
        return true;
      }
      skip_directives();
    }
    if (!at(TK::Semicolon)) {
      recordGrammarFallback("missing Annex A class header semicolon");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    parseDelimitedBody(closeKw,
                       interface_class ? "interface_class_item" : "class_item");
    return true;
  }

  // class / function / task ... endclass / endfunction / endtask
  auto parseNamedBlock(TK closeKw) -> void {
    if (parseTaskFunctionBlockRule(closeKw)) {
      return;
    }
    if (parseClassBlockRule(closeKw)) {
      return;
    }
    std::vector<std::string_view> roots;
    std::string_view body_rule;
    bool tf_ports_in_header = false;
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
    if (!roots.empty()) {
      beginGrammar(roots);
    }
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
      } else if (closeKw == TK::EndFunctionKeyword) {
        tf_ports_in_header = header.hasActiveProductionContaining(
            "function_body_declaration", TK::OpenParenthesis);
      } else if (closeKw == TK::EndTaskKeyword) {
        tf_ports_in_header = header.hasActiveProductionContaining(
            "task_body_declaration", TK::OpenParenthesis);
      }
    }
    parseDelimitedBody(closeKw, body_rule, false, tf_ports_in_header);
  }

  // generate ... endgenerate
  auto parseSimpleBlock(TK closeKw) -> void {
    consumeInto(
        line_);  // generate_region ::= generate {generate_item} endgenerate
    addLine();
    parseDelimitedBody(closeKw, "generate_item");
  }

  // begin [:label] ... end [:label]
  auto parseOpeningBlockLabelRule() -> void {
    if (!at(TK::Colon)) {
      return;
    }
    consumeInto(line_);
    if (at(TK::Identifier)) {
      consumeInto(line_);
    } else {
      recordGrammarFallback("incomplete Annex A block identifier");
    }
  }

  auto parseBeginEnd(TK closeKw) -> void {
    const bool if_statement_body = std::exchange(pending_if_begin_, false);
    consumeInto(line_);  // begin
    parseOpeningBlockLabelRule();
    addLine();

    parseDelimitedBody(closeKw, {}, false, false, if_statement_body);
  }

  // fork ... join / join_any / join_none
  auto parseFork(TK closeKw) -> void {
    consumeInto(line_);  // fork
    parseOpeningBlockLabelRule();
    addLine();
    parseDelimitedBody(closeKw);
  }

  // Conditional directives between a procedural keyword and its statement
  // need a live Annex A continuation through each preprocessor branch.
  auto parseConditionalProceduralBlock() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"always_construct", "initial_construct", "final_construct"});
    consumeInto(line_);  // keyword
    while (isCompilerDirective(peek())) {
      if (isConditionalStartDirective(peek())) {
        bool header_ended = true;
        if (!parseAnnexConditional(TK::EndOfFile, header_ended,
                                   indent_level_)) {
          static_cast<void>(endGrammar(false));
          recoverMalformedItem(saved);
          return;
        }
      } else {
        addLine();
        parseDirectiveLine();
      }
    }
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
    if (header.complete()) {
      addLine();
      return;
    }
    if (header.completedFrom("always_construct", 0) ||
        header.completedFrom("initial_construct", 0) ||
        header.completedFrom("final_construct", 0)) {
      recordGrammarFallback("conditional procedural branches end differently");
      recoverMalformedItem(saved);
      return;
    }
    std::vector<std::string_view> body_roots;
    if (has_delay_control || has_event_control ||
        header.allPathsHaveActiveRule("statement_or_null") ||
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
    constexpr std::array compound_rules = {"seq_block", "par_block",
                                           "conditional_statement",
                                           "case_statement", "loop_statement"};
    const bool compound_statement =
        std::ranges::any_of(compound_rules, [&](std::string_view rule) {
          return header.hasActiveRule(rule) && annexCanStart(rule, next);
        });
    if (has_delay_control && !compound_statement) {
      grammar_contexts_.push_back({block_stack_.size(), body_roots});
      parseStatement();
      grammar_contexts_.pop_back();
      return;
    }
    addLine();

    parseIndentedStatement(std::move(body_roots));
  }

  // initial_construct ::= initial statement_or_null;
  // always_construct ::= always_keyword statement;
  // final_construct ::= final function_statement.
  auto parseProceduralBlock() -> void {
    for (size_t i = pos_ + 1;
         i < tokens_.size() && isCompilerDirective(tokens_[i]); ++i) {
      if (isConditionalStartDirective(tokens_[i])) {
        parseConditionalProceduralBlock();
        return;
      }
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const TK keyword = peek().kind;
    consumeInto(line_);
    while (isCompilerDirective(peek()) &&
           !isConditionalStartDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    const bool delay_control = at(TK::Hash);
    if (delay_control && !consumeAnnexRule("delay_control", line_)) {
      recoverMalformedItem(saved);
      return;
    }
    const bool event_control = at(TK::At);
    if (event_control && !consumeAnnexRule("event_control", line_)) {
      recoverMalformedItem(saved);
      return;
    }
    if (keyword == TK::FinalKeyword && (delay_control || event_control)) {
      recordGrammarFallback("timing control outside Annex A final construct");
      recoverMalformedItem(saved);
      return;
    }
    if (at(TK::EndOfFile) ||
        (stop_at_conditional_boundary_ &&
         isConditionalBoundaryDirective(peek())) ||
        std::ranges::any_of(block_stack_, [&](const BlockFrame& frame) {
          return matchesBlockClose(frame.close_kind, peek().kind);
        })) {
      recordGrammarFallback("missing Annex A procedural body");
      recoverMalformedItem(saved);
      return;
    }
    std::vector<std::string_view> body_roots;
    if (delay_control || event_control || keyword == TK::InitialKeyword) {
      body_roots = {"statement_or_null"};
    } else if (keyword == TK::FinalKeyword) {
      body_roots = {"function_statement"};
    } else {
      body_roots = {"statement"};
    }
    const TK next = peek().kind;
    const bool compound_statement =
        next == TK::BeginKeyword || next == TK::ForkKeyword ||
        next == TK::IfKeyword || next == TK::CaseKeyword ||
        next == TK::CaseXKeyword || next == TK::CaseZKeyword ||
        next == TK::ForKeyword || next == TK::ForeachKeyword ||
        next == TK::WhileKeyword || next == TK::RepeatKeyword ||
        next == TK::ForeverKeyword || next == TK::DoKeyword ||
        next == TK::UniqueKeyword || next == TK::Unique0Keyword ||
        next == TK::PriorityKeyword;
    if (delay_control && !compound_statement) {
      grammar_contexts_.push_back({block_stack_.size(), body_roots});
      parseStatement();
      grammar_contexts_.pop_back();
      return;
    }
    addLine();
    parseIndentedStatement(std::move(body_roots));
  }

  // conditional_statement and if_generate_construct from Annex A.
  auto parseIf(bool generate) -> void {
    const std::string_view rule =
        generate ? "if_generate_construct" : "conditional_statement";
    const std::vector<std::string_view> body_roots = {
        generate ? "generate_block" : "statement_or_null"};
    while (at(TK::IfKeyword)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool conditional_before_condition = false;
      for (size_t i = pos_ + 1; i < tokens_.size(); ++i) {
        if (tokens_[i].kind == TK::OpenParenthesis ||
            tokens_[i].kind == TK::Semicolon ||
            tokens_[i].kind == TK::EndOfFile) {
          break;
        }
        if (isConditionalStartDirective(tokens_[i])) {
          conditional_before_condition = true;
          break;
        }
      }
      bool header_complete = false;
      if (conditional_before_condition) {
        beginGrammar({rule});
        while (!at(TK::EndOfFile) &&
               !grammar_scopes_.back().allPathsHaveActiveRule(
                   body_roots.front()) &&
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
          if (!grammar_scopes_.back().accepts(peek().kind)) {
            break;
          }
          consumeInto(line_);
        }
        const AnnexState header = endGrammar(false);
        if (header.failed || header.interrupted ||
            (!header.allPathsHaveActiveRule(body_roots.front()) &&
             !header.complete())) {
          recordGrammarFallback("invalid Annex A if header");
          recoverMalformedItem(saved);
          return;
        }
        header_complete = header.complete();
      } else {
        consumeInto(line_);
        while (isCompilerDirective(peek()) &&
               !isConditionalStartDirective(peek())) {
          addLine();
          parseDirectiveLine();
        }
        if (!at(TK::OpenParenthesis)) {
          recordGrammarFallback("invalid Annex A if condition");
          recoverMalformedItem(saved);
          return;
        }
        const bool predicate = consumeAnnexDelimited(
            TK::OpenParenthesis, TK::CloseParenthesis,
            generate ? "constant_expression" : "cond_predicate", line_);
        if (!predicate || pos_ == 0 ||
            tokens_[pos_ - 1].kind != TK::CloseParenthesis) {
          recordGrammarFallback("incomplete Annex A if condition");
          recoverMalformedItem(saved);
          return;
        }
      }
      addLine();
      if (!header_complete) {
        if (atEnclosingBoundary()) {
          recordGrammarFallback("missing Annex A if body");
          recoverMalformedItem(saved);
          return;
        }
        const bool prior_if_begin = std::exchange(pending_if_begin_, !generate);
        parseIndentedStatement(body_roots);
        pending_if_begin_ = prior_if_begin;
      }
      if (at(TK::ElseKeyword)) {
        indent_level_ = saved.indent_level;
      }
      if (!at(TK::ElseKeyword)) {
        return;
      }
      consumeInto(line_);
      if (generate || !at(TK::IfKeyword)) {
        if (atEnclosingBoundary()) {
          recordGrammarFallback("missing Annex A else body");
          recoverMalformedItem(saved);
          return;
        }
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
    const std::string_view rule = randcase   ? "randcase_statement"
                                  : generate ? "case_generate_construct"
                                             : "case_statement";
    bool conditional_before_condition = false;
    if (!randcase) {
      for (size_t i = pos_ + 1; i < tokens_.size(); ++i) {
        if (tokens_[i].kind == TK::OpenParenthesis ||
            tokens_[i].kind == TK::Semicolon ||
            tokens_[i].kind == TK::EndOfFile) {
          break;
        }
        if (isConditionalStartDirective(tokens_[i])) {
          conditional_before_condition = true;
          break;
        }
      }
    }
    std::string_view body_rule;
    bool header_complete = false;
    if (conditional_before_condition) {
      beginGrammar({rule});
      const auto active_body = [&]() -> std::string_view {
        if (!generate && (at(TK::InsideKeyword) || at(TK::MatchesKeyword))) {
          return {};
        }
        for (const std::string_view child :
             {"case_item", "case_pattern_item", "case_inside_item",
              "case_generate_item"}) {
          if (grammar_scopes_.back().allPathsHaveActiveRule(child)) {
            return child;
          }
        }
        return {};
      };
      while (!at(TK::EndOfFile) && active_body().empty() &&
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
        if (!grammar_scopes_.back().accepts(peek().kind)) {
          break;
        }
        consumeInto(line_);
      }
      body_rule = active_body();
      const AnnexState header = endGrammar(false);
      if (header.failed || header.interrupted ||
          (body_rule.empty() && !header.complete())) {
        recordGrammarFallback("invalid Annex A case header");
        recoverMalformedItem(saved);
        return;
      }
      header_complete = header.complete();
    } else {
      const TK keyword = peek().kind;
      consumeInto(line_);
      if (randcase) {
        body_rule = "randcase_item";
      } else {
        while (isCompilerDirective(peek()) &&
               !isConditionalStartDirective(peek())) {
          addLine();
          parseDirectiveLine();
        }
        if (!at(TK::OpenParenthesis)) {
          recordGrammarFallback("invalid Annex A case condition");
          recoverMalformedItem(saved);
          return;
        }
        const bool expression = consumeAnnexDelimited(
            TK::OpenParenthesis, TK::CloseParenthesis,
            generate ? "constant_expression" : "case_expression", line_);
        if (!expression || pos_ == 0 ||
            tokens_[pos_ - 1].kind != TK::CloseParenthesis) {
          recordGrammarFallback("incomplete Annex A case condition");
          recoverMalformedItem(saved);
          return;
        }
        while (isCompilerDirective(peek()) &&
               !isConditionalStartDirective(peek())) {
          addLine();
          parseDirectiveLine();
        }
        if (generate) {
          body_rule = "case_generate_item";
        } else if (at(TK::MatchesKeyword)) {
          consumeInto(line_);
          body_rule = "case_pattern_item";
        } else if (at(TK::InsideKeyword) && keyword == TK::CaseKeyword) {
          consumeInto(line_);
          body_rule = "case_inside_item";
        } else if (at(TK::InsideKeyword)) {
          recordGrammarFallback("case inside outside Annex A case rule");
          recoverMalformedItem(saved);
          return;
        } else {
          body_rule = "case_item";
        }
      }
    }
    addLine();
    if (header_complete) {
      return;
    }

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
    const size_t header_open = afterOrdinaryDirectives(1);
    if (!at(TK::OpenParenthesis, header_open) ||
        !unavailableInFollowingParentheses(pos_ + header_open)) {
      consumeInto(line_);  // randsequence
      parseGrammarChildDirectiveLines();
      if (!at(TK::OpenParenthesis)) {
        recordGrammarFallback("invalid Annex A randsequence header");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      bool valid = true;
      if (!at(TK::CloseParenthesis)) {
        valid = consumeAnnexRule("rs_production_identifier", line_);
      }
      parseGrammarChildDirectiveLines();
      if (!valid || !at(TK::CloseParenthesis)) {
        recordGrammarFallback("invalid Annex A randsequence header");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      addLine();
      parseDelimitedBody(TK::EndSequenceKeyword, "rs_production");
      return;
    }
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

  // rs_production ::= [ data_type_or_void ] rs_production_identifier
  // [ '(' tf_port_list ')' ] ':' rs_rule { '|' rs_rule } ';'. The parent
  // production remains live while each rs_rule is parsed as a child.
  [[nodiscard]] auto parseRsProductionItemRule() -> bool {
    if (!consumeAnnexRule("rs_production_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (at(TK::OpenParenthesis)) {
      return consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                   "list_of_arguments", line_);
    }
    return true;
  }

  [[nodiscard]] auto parseRsCaseItemRule() -> bool {
    parseGrammarChildDirectiveLines();
    if (at(TK::DefaultKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (at(TK::Colon)) {
        consumeInto(line_);
      }
    } else {
      if (!consumeAnnexRule("case_item_expression", line_, TK::Colon)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      while (at(TK::Comma)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
        if (!consumeAnnexRule("case_item_expression", line_, TK::Colon)) {
          return false;
        }
        parseGrammarChildDirectiveLines();
      }
      if (!at(TK::Colon)) {
        return false;
      }
      consumeInto(line_);
    }
    parseGrammarChildDirectiveLines();
    if (!parseRsProductionItemRule()) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!at(TK::Semicolon)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  [[nodiscard]] auto parseRsCaseRule() -> bool {
    if (!at(TK::CaseKeyword)) {
      return false;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                               "case_expression", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!parseRsCaseItemRule()) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (!at(TK::EndCaseKeyword) && !at(TK::EndOfFile)) {
      if (!annexCanStart("rs_case_item", peek().kind) ||
          !parseRsCaseItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (!at(TK::EndCaseKeyword)) {
      return false;
    }
    consumeInto(line_);
    return true;
  }

  [[nodiscard]] auto interruptedRsCodeBlock() const -> bool {
    size_t braces = 0;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const auto& token = tokens_[i];
      if (isConditionalStartDirective(token) || token.kind == TK::MacroUsage ||
          (token.kind == TK::Directive && !isCompilerDirective(token))) {
        return true;
      }
      if (token.kind == TK::OpenBrace ||
          token.kind == TK::ApostropheOpenBrace) {
        ++braces;
      } else if (token.kind == TK::CloseBrace && braces > 0) {
        --braces;
        if (braces == 0) {
          return false;
        }
      }
      if (token.kind == TK::EndOfFile ||
          (!block_stack_.empty() &&
           matchesBlockClose(block_stack_.back().close_kind, token.kind))) {
        return true;
      }
    }
    return true;
  }

  // rs_code_block ::= '{' { data_declaration }
  //                   { statement_or_null } '}'.
  [[nodiscard]] auto parseRsCodeBlockRule() -> bool {
    if (!at(TK::OpenBrace)) {
      return false;
    }
    if (interruptedRsCodeBlock()) {
      return consumeAnnexRule("rs_code_block", line_);
    }
    consumeInto(line_);
    addLine();
    const TK outer_close =
        block_stack_.empty() ? TK::EndOfFile : block_stack_.back().close_kind;
    pushOpenFrame(TK::CloseBrace);
    ++indent_level_;
    bool statements_started = false;
    while (!at(TK::CloseBrace) && !at(TK::EndOfFile) && !at(outer_close)) {
      const size_t before = pos_;
      if (at(TK::Directive)) {
        parseStatement();
      } else {
        bool declaration = false;
        if (!statements_started) {
          declaration =
              parseTypeDeclarationRule() || parseNettypeDeclarationRule() ||
              parseQualifiedDataDeclarationRule() ||
              (at(TK::ImportKeyword) && parsePackageImportExportRule()) ||
              parseExplicitDataDeclarationRule() ||
              parseUserDataDeclarationRule();
        }
        if (!declaration) {
          statements_started = true;
          grammar_contexts_.push_back(
              {block_stack_.size(), {"statement_or_null"}});
          parseStatement();
          grammar_contexts_.pop_back();
        }
      }
      if (pos_ == before) {
        break;
      }
    }
    if (!at(TK::CloseBrace)) {
      recordGrammarFallback("incomplete Annex A randsequence code block");
      block_stack_.pop_back();
      if (indent_level_ > 0) {
        --indent_level_;
      }
      return false;
    }
    parseOpenFrameClose();
    return true;
  }

  [[nodiscard]] auto parseRsProdRule() -> bool {
    if (at(TK::Identifier)) {
      return parseRsProductionItemRule();
    }
    if (at(TK::OpenBrace)) {
      return parseRsCodeBlockRule();
    }
    if (at(TK::IfKeyword) || at(TK::RepeatKeyword)) {
      const bool conditional = at(TK::IfKeyword);
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                 "expression", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!parseRsProductionItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (conditional && at(TK::ElseKeyword)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
        if (!parseRsProductionItemRule()) {
          return false;
        }
      }
      return true;
    }
    if (at(TK::CaseKeyword)) {
      return parseRsCaseRule();
    }
    return false;
  }

  [[nodiscard]] auto parseRsProductionListRule() -> bool {
    // Conditional directives and unavailable expansions keep the
    // interrupted child grammar path.
    if (hasAnnexListInterruption(pos_, false)) {
      return consumeAnnexRule("rs_production_list", line_, TK::ColonEquals);
    }
    if (at(TK::RandKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!at(TK::JoinKeyword)) {
        return false;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (at(TK::OpenParenthesis) &&
          !consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                 "expression", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!parseRsProductionItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!parseRsProductionItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      while (at(TK::Identifier)) {
        if (!parseRsProductionItemRule()) {
          return false;
        }
        parseGrammarChildDirectiveLines();
      }
      return true;
    }
    if (!parseRsProdRule()) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (annexCanStart("rs_prod", peek().kind)) {
      if (!parseRsProdRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    return true;
  }

  [[nodiscard]] auto parseRsRule() -> bool {
    if (!parseRsProductionListRule()) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (at(TK::ColonEquals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("rs_weight_specification", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (at(TK::OpenBrace) && !parseRsCodeBlockRule()) {
        return false;
      }
    }
    return true;
  }

  auto parseRsProductionRule() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    const size_t after_identifier = afterOrdinaryDirectives(1);
    const bool untyped =
        at(TK::Identifier) && (at(TK::Colon, after_identifier) ||
                               at(TK::OpenParenthesis, after_identifier));
    const auto after_user_type =
        at(TK::Identifier) ? afterUserTypePrefix(0) : std::nullopt;
    const bool typed =
        (peek().kind != TK::Identifier &&
         annexCanStart("data_type_or_void", peek().kind)) ||
        (after_user_type &&
         at(TK::Identifier, afterOrdinaryDirectives(*after_user_type)));
    if (untyped || typed) {
      bool valid = !typed || consumeAnnexRule("data_type_or_void", line_);
      parseGrammarChildDirectiveLines();
      if (valid) {
        valid = consumeAnnexRule("rs_production_identifier", line_);
      }
      parseGrammarChildDirectiveLines();
      if (valid && at(TK::OpenParenthesis)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
        valid = !at(TK::CloseParenthesis);
        while (valid) {
          valid = parseTfPortItemRule();
          parseGrammarChildDirectiveLines();
          if (!valid || !at(TK::Comma)) {
            break;
          }
          consumeInto(line_);
          parseGrammarChildDirectiveLines();
        }
        if (valid && at(TK::CloseParenthesis)) {
          consumeInto(line_);
        } else {
          valid = false;
        }
      }
      parseGrammarChildDirectiveLines();
      if (valid && at(TK::Colon)) {
        consumeInto(line_);
      } else {
        valid = false;
      }
      parseGrammarChildDirectiveLines();
      if (valid) {
        valid = parseRsRule();
      }
      parseGrammarChildDirectiveLines();
      while (valid && at(TK::Or)) {
        consumeInto(line_);
        addLine();
        parseGrammarChildDirectiveLines();
        valid = parseRsRule();
        parseGrammarChildDirectiveLines();
      }
      if (!valid || !at(TK::Semicolon)) {
        recordGrammarFallback("invalid Annex A randsequence production");
        recoverMalformedItem(saved);
        return;
      }
      consumeInto(line_);
      addLine();
      return;
    }
    recordGrammarFallback("unavailable Annex A randsequence production prefix");
    recoverMalformedItem(saved);
  }

  // clocking_item ::= default default_skew ';'
  //                | clocking_direction list_of_clocking_decl_assign ';'
  //                | { attribute_instance } assertion_item_declaration.
  // clocking_skew ::= edge_identifier [ delay_control ] | delay_control.
  [[nodiscard]] auto parseClockingSkewRule() -> bool {
    parseGrammarChildDirectiveLines();
    const bool edge = annexCanStart("edge_identifier", peek().kind);
    if (edge && !consumeAnnexRule("edge_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (at(TK::Hash)) {
      return consumeAnnexRule("delay_control", line_);
    }
    return edge;
  }

  // default_skew requires a skew after each direction; clocking_direction
  // permits it to be absent and also has the single 'inout' alternative.
  [[nodiscard]] auto parseClockingDirectionRule(bool require_skew) -> bool {
    parseGrammarChildDirectiveLines();
    if (at(TK::InOutKeyword) && !require_skew) {
      consumeInto(line_);
      return true;
    }
    if (!at(TK::InputKeyword) && !at(TK::OutputKeyword)) {
      return false;
    }
    const bool input = at(TK::InputKeyword);
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (require_skew || at(TK::Hash) ||
        annexCanStart("edge_identifier", peek().kind)) {
      if (!parseClockingSkewRule()) {
        return false;
      }
    }
    parseGrammarChildDirectiveLines();
    if (input && at(TK::OutputKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (require_skew || at(TK::Hash) ||
          annexCanStart("edge_identifier", peek().kind)) {
        return parseClockingSkewRule();
      }
    }
    return true;
  }

  // clocking_decl_assign ::= signal_identifier [ '=' expression ].
  [[nodiscard]] auto parseClockingDeclAssignRule() -> bool {
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("signal_identifier", line_, TK::Comma, [&] {
          return at(TK::Equals) || at(TK::Semicolon);
        })) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("expression", line_, TK::Comma,
                            [&] { return at(TK::Semicolon); })) {
        return false;
      }
    }
    return true;
  }

  [[nodiscard]] auto parseClockingDeclAssignListRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseClockingDeclAssignRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  auto parseClockingItemRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      if (valid && annexCanStart("assertion_item_declaration", peek().kind) &&
          parseClockingItemRule()) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed clocking item");
      recoverMalformedItem(saved);
      return true;
    }
    if (at(TK::PropertyKeyword) || at(TK::SequenceKeyword)) {
      return parsePackageOrGenerateDeclarationRule();
    }
    if (at(TK::LetKeyword)) {
      return parseLetDeclarationRule();
    }
    const bool default_item = at(TK::DefaultKeyword);
    const bool direction_item =
        annexCanStart("clocking_direction", peek().kind);
    if (!default_item && !direction_item) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const bool conditional_members =
        direction_item && hasConditionalListMember(pos_);
    const bool interrupted =
        hasAnnexListInterruption(pos_, conditional_members);
    bool valid = true;
    if (default_item) {
      consumeInto(line_);
      valid = interrupted
                  ? consumeAnnexRule("default_skew", line_, TK::Semicolon)
                  : parseClockingDirectionRule(true);
    } else {
      valid = interrupted ? consumeAnnexRule("clocking_direction", line_)
                          : parseClockingDirectionRule(false);
      if (valid) {
        valid = interrupted ? consumeAnnexRule("list_of_clocking_decl_assign",
                                               line_, TK::Semicolon)
                : conditional_members ? parseConditionalAnnexCommaListRule(
                                            "list_of_clocking_decl_assign",
                                            "clocking_decl_assign")
                                      : parseClockingDeclAssignListRule();
      }
    }
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A clocking item");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // let_port_item ::= { attribute_instance } let_formal_type
  // formal_port_identifier { variable_dimension } [ '=' expression ].
  [[nodiscard]] auto parseLetPortItemRule() -> bool {
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      if (!consumeAnnexRule("attribute_instance", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    const bool implicit_type =
        implicitIdentifierBefore({TK::Comma, TK::CloseParenthesis, TK::Equals});
    if (!implicit_type && !consumeAnnexRule("let_formal_type", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    if (!consumeAnnexRule("formal_port_identifier", line_)) {
      return false;
    }
    parseGrammarChildDirectiveLines();
    while (at(TK::OpenBracket)) {
      if (!consumeAnnexRule("variable_dimension", line_)) {
        return false;
      }
      parseGrammarChildDirectiveLines();
    }
    if (at(TK::Equals)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexRule("expression", line_, TK::Comma,
                            [&] { return at(TK::CloseParenthesis); })) {
        return false;
      }
    }
    return true;
  }

  [[nodiscard]] auto parseLetPortListRule() -> bool {
    do {  // NOLINT(cppcoreguidelines-avoid-do-while)
      if (!parseLetPortItemRule()) {
        return false;
      }
      parseGrammarChildDirectiveLines();
      if (!at(TK::Comma)) {
        break;
      }
      consumeInto(line_);
    } while (!at(TK::EndOfFile));
    return true;
  }

  // let_declaration ::= let let_identifier
  // [ '(' [ let_port_list ] ')' ] '=' expression ';'.
  auto parseLetDeclarationRule() -> bool {
    if (!at(TK::LetKeyword)) {
      return false;
    }
    const bool conditional_ports =
        at(TK::Identifier, 1) && at(TK::OpenParenthesis, 2) &&
        hasConditionalListMember(pos_ + 3, TK::CloseParenthesis);
    if (hasAnnexHeaderInterruption(pos_, conditional_ports)) {
      static_cast<void>(parseAnnexItem({"let_declaration"}, true));
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const auto skip_directives = [&] {
      while (isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    };
    consumeInto(line_);
    skip_directives();
    if (!consumeAnnexRule("let_identifier", line_)) {
      recordGrammarFallback("invalid Annex A let identifier");
      recoverMalformedItem(saved);
      return true;
    }
    skip_directives();
    if (at(TK::OpenParenthesis)) {
      if (at(TK::CloseParenthesis, 1)) {
        consumeInto(line_);
        consumeInto(line_);
      } else {
        consumeInto(line_);
        if (!(conditional_ports
                  ? parseConditionalAnnexCommaListRule(
                        "let_port_list", "let_port_item", TK::CloseParenthesis)
                  : parseLetPortListRule()) ||
            !at(TK::CloseParenthesis)) {
          recordGrammarFallback("invalid Annex A let port list");
          recoverMalformedItem(saved);
          return true;
        }
        consumeInto(line_);
      }
    }
    skip_directives();
    if (!at(TK::Equals)) {
      recordGrammarFallback("invalid Annex A let assignment");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    skip_directives();
    if (!consumeAnnexRule("expression", line_, TK::Semicolon) ||
        !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A let expression");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // coverage_option ::= option '.' member_identifier '=' expression |
  // type_option '.' member_identifier '=' constant_expression.
  auto parseCoverageOptionRule() -> bool {
    if (!at(TK::Identifier) || !at(TK::Dot, afterOrdinaryDirectives(1)) ||
        (peek().rawText() != "option" && peek().rawText() != "type_option")) {
      return false;
    }
    if (hasAnnexListInterruption(pos_, false)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    const bool constant = peek().rawText() == "type_option";
    consumeInto(line_);
    while (afterOrdinaryDirectives(0) > 0) {
      addLine();
      parseDirectiveLine();
    }
    consumeInto(line_);
    const bool member = consumeAnnexRule("member_identifier", line_);
    parseGrammarChildDirectiveLines();
    if (!member || !at(TK::Equals)) {
      recordGrammarFallback("invalid Annex A coverage option member");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    const bool value = consumeAnnexRule(
        constant ? "constant_expression" : "expression", line_, TK::Semicolon);
    parseGrammarChildDirectiveLines();
    if (!value || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A coverage option value");
      recoverMalformedItem(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // cross_body_item ::= function_declaration |
  //                     bins_selection_or_option ';'. Only the second child
  // has an attribute_instance prefix.
  auto parseCrossBodyItemRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      if (valid && annexCanStart("bins_selection_or_option", peek().kind) &&
          parseCrossBodyItemRule()) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed cross body item");
      recoverMalformedItem(saved);
      return true;
    }
    if (at(TK::FunctionKeyword)) {
      parseNamedBlock(TK::EndFunctionKeyword);
      return true;
    }
    if (parseCoverageOptionRule()) {
      return true;
    }
    if (!at(TK::BinsKeyword) && !at(TK::IllegalBinsKeyword) &&
        !at(TK::IgnoreBinsKeyword)) {
      return false;
    }
    if (hasAnnexListInterruption(pos_, false)) {
      return false;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = consumeAnnexRule("bins_keyword", line_);
    parseGrammarChildDirectiveLines();
    if (valid) {
      valid = consumeAnnexRule("bin_identifier", line_);
    }
    parseGrammarChildDirectiveLines();
    if (valid && at(TK::Equals)) {
      consumeInto(line_);
    } else {
      valid = false;
    }
    parseGrammarChildDirectiveLines();
    if (valid) {
      valid = consumeAnnexRule("select_expression", line_, TK::IffKeyword);
    }
    parseGrammarChildDirectiveLines();
    if (valid && at(TK::IffKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      valid = consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                    "expression", line_);
    }
    parseGrammarChildDirectiveLines();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A cross bins selection");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // Parse the shared bins prefix before choosing its right-hand production.
  // A parenthesized expression shares its prefix with trans_list; only that
  // right-hand child needs both Annex A alternatives live.
  auto parseBinsOrOptionsRule() -> bool {
    if (parseCoverageOptionRule()) {
      return true;
    }
    const bool wildcard = at(TK::WildcardKeyword);
    const size_t bins_offset = wildcard ? afterOrdinaryDirectives(1) : 0;
    if (!(at(TK::BinsKeyword, bins_offset) ||
          at(TK::IllegalBinsKeyword, bins_offset) ||
          at(TK::IgnoreBinsKeyword, bins_offset))) {
      return false;
    }
    // Conditional directives and unavailable macro expansions need the
    // interrupted item path, which can resume at the enclosing coverpoint.
    if (hasAnnexListInterruption(pos_, false)) {
      return false;
    }

    const LeafCheckpoint saved = leafCheckpoint();
    if (wildcard) {
      consumeInto(line_);
      while (afterOrdinaryDirectives(0) > 0) {
        addLine();
        parseDirectiveLine();
      }
    }
    bool valid = consumeAnnexRule("bins_keyword", line_);
    parseGrammarChildDirectiveLines();
    if (valid) {
      valid = consumeAnnexRule("bin_identifier", line_);
    }
    parseGrammarChildDirectiveLines();
    bool bracketed = false;
    bool bracket_contents = false;
    if (valid && at(TK::OpenBracket)) {
      bracketed = true;
      bracket_contents = !at(TK::CloseBracket, 1);
      if (bracket_contents) {
        valid = consumeAnnexDelimited(TK::OpenBracket, TK::CloseBracket,
                                      "covergroup_expression", line_);
      } else {
        consumeInto(line_);
        consumeInto(line_);
      }
    }
    if (valid && at(TK::Equals)) {
      consumeInto(line_);
    } else {
      valid = false;
    }
    parseGrammarChildDirectiveLines();
    const TK rhs = peek().kind;
    const bool named_coverpoint = at(TK::Identifier) && at(TK::WithKeyword, 1);
    if (valid && rhs == TK::OpenBrace) {
      valid = consumeAnnexDelimited(TK::OpenBrace, TK::CloseBrace,
                                    "covergroup_range_list", line_);
      parseGrammarChildDirectiveLines();
      if (valid && at(TK::WithKeyword)) {
        consumeInto(line_);
        parseGrammarChildDirectiveLines();
        valid = consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                      "with_covergroup_expression", line_);
      }
    } else if (valid && rhs == TK::DefaultKeyword) {
      valid = !wildcard;
      if (valid) {
        consumeInto(line_);  // default
      }
      if (valid && at(TK::SequenceKeyword)) {
        valid = !bracketed;
        if (valid) {
          consumeInto(line_);
        }
      }
    } else if (valid && named_coverpoint) {
      valid = consumeAnnexRule("cover_point_identifier", line_);
      parseGrammarChildDirectiveLines();
      if (valid && at(TK::WithKeyword)) {
        consumeInto(line_);
      } else {
        valid = false;
      }
      parseGrammarChildDirectiveLines();
      if (valid) {
        valid = consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                      "with_covergroup_expression", line_);
      }
    } else if (valid && rhs == TK::OpenParenthesis) {
      const AnnexState value = parseAnnexItem(
          {"set_covergroup_expression", "trans_list"}, false, true);
      valid = !value.failed && !value.interrupted && value.complete() &&
              (value.completed("set_covergroup_expression") ||
               (!bracket_contents && value.completed("trans_list")));
    } else if (valid) {
      valid =
          consumeAnnexRule("set_covergroup_expression", line_, TK::IffKeyword);
    }
    parseGrammarChildDirectiveLines();
    if (valid && at(TK::IffKeyword)) {
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      valid = consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                    "expression", line_);
    }
    parseGrammarChildDirectiveLines();
    if (!valid || !at(TK::Semicolon)) {
      recordGrammarFallback("invalid Annex A covergroup bins item");
      recoverMalformedLeaf(saved);
      return true;
    }
    consumeInto(line_);
    addLine();
    return true;
  }

  // bins_or_empty ::= '{' { attribute_instance }
  //                   { bins_or_options ';' } '}' | ';'. The attributes belong
  // to the body prefix, before the repeated bins_or_options children.
  auto parseCoverpointBinsBodyRule() -> void {
    pushOpenFrame(TK::CloseBrace);
    block_stack_.back().grammar_body = "bins_or_options";
    ++indent_level_;
    while (!at(TK::CloseBrace) && !at(TK::EndOfFile) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
      if (at(TK::Directive) && isCompilerDirective(peek())) {
        parseStatement();
        continue;
      }
      if (!at(TK::OpenParenthesis) || !at(TK::Star, 1)) {
        break;
      }
      const LeafCheckpoint saved = leafCheckpoint();
      if (!consumeAnnexRule("attribute_instance", line_)) {
        recordGrammarFallback("invalid Annex A coverpoint attribute");
        recoverMalformedItem(saved);
        break;
      }
    }
    if (at(TK::CloseBrace) && !line_.tokens.empty()) {
      addLine();
    }
    while (!at(TK::CloseBrace) && !at(TK::EndOfFile) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
      if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
        const LeafCheckpoint saved = leafCheckpoint();
        recordGrammarFallback("attribute after Annex A coverpoint bins prefix");
        recoverMalformedLeaf(saved);
      } else {
        parseStatement();
      }
    }
    if (at(TK::CloseBrace)) {
      parseOpenFrameClose();
    } else if (!(stop_at_conditional_boundary_ &&
                 isConditionalBoundaryDirective(peek()))) {
      recordGrammarFallback("incomplete Annex A coverpoint bins body");
    }
  }

  // coverage_spec ::= cover_point | cover_cross. Direct headers enter their
  // expression and body children; a chart remains for interrupted headers.
  auto parseDirectCoverageSpecRule() -> bool {
    const bool labeled = at(TK::Identifier) && at(TK::Colon, 1);
    const size_t keyword_offset = labeled ? 2 : 0;
    bool point = at(TK::CoverPointKeyword, keyword_offset);
    const bool cross = at(TK::CrossKeyword, keyword_offset);
    bool parsed_point_prefix = false;
    if (!point && !cross) {
      const LeafCheckpoint saved = leafCheckpoint();
      beginGrammar({"cover_point"});
      while (!at(TK::CoverPointKeyword) && !atEnclosingBoundary() &&
             !at(TK::Semicolon) && !at(TK::OpenBrace)) {
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
        if (!grammar_scopes_.back().accepts(peek().kind)) {
          break;
        }
        consumeInto(line_);
      }
      const bool keyword_expected =
          at(TK::CoverPointKeyword) &&
          grammar_scopes_.back().accepts(TK::CoverPointKeyword);
      const AnnexState prefix = endGrammar(false);
      if (!keyword_expected || prefix.failed || prefix.interrupted ||
          !prefix.hasViableRule("cover_point")) {
        recordGrammarFallback("invalid Annex A coverpoint prefix");
        recoverMalformedItem(saved);
        return true;
      }
      point = true;
      parsed_point_prefix = true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    bool valid = true;
    if (labeled && !parsed_point_prefix) {
      valid = consumeAnnexRule(
          point ? "cover_point_identifier" : "cross_identifier", line_);
      if (valid && at(TK::Colon)) {
        consumeInto(line_);
      } else {
        valid = false;
      }
    }
    if (valid) {
      consumeInto(line_);  // coverpoint / cross
    }
    if (valid) {
      valid = consumeAnnexRule(
          point ? "expression" : "list_of_cross_items", line_, TK::IffKeyword,
          [&] { return at(TK::Semicolon) || at(TK::OpenBrace); });
    }
    if (valid && at(TK::IffKeyword)) {
      consumeInto(line_);
      valid = consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                    "expression", line_);
    }
    if (!valid || (!at(TK::Semicolon) && !at(TK::OpenBrace))) {
      recordGrammarFallback("invalid Annex A coverage spec header");
      recoverMalformedItem(saved);
      return true;
    }
    const bool braced = at(TK::OpenBrace);
    consumeInto(line_);
    addLine();
    if (braced) {
      if (point) {
        parseCoverpointBinsBodyRule();
      } else {
        parseDelimitedBody(TK::CloseBrace, "cross_body_item");
      }
    }
    return true;
  }

  auto parseCoverageSpecRule() -> bool {
    if (!annexCanStart("cover_point", peek().kind) &&
        !annexCanStart("cover_cross", peek().kind)) {
      return false;
    }
    if (parseDirectCoverageSpecRule()) {
      return true;
    }
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"cover_point", "cover_cross"});
    while (!at(TK::EndOfFile) &&
           !grammar_scopes_.back().hasActiveRule("bins_or_empty") &&
           !grammar_scopes_.back().hasActiveRule("cross_body")) {
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
      if (!grammar_scopes_.back().accepts(peek().kind)) {
        break;
      }
      consumeInto(line_);
    }
    const AnnexState header = endGrammar(false);
    const std::string_view body_rule =
        header.hasActiveRule("bins_or_empty") ? "bins_or_empty"
        : header.hasActiveRule("cross_body")  ? "cross_body"
                                              : "";
    if (header.failed || header.interrupted || body_rule.empty() ||
        (!at(TK::OpenBrace) && !at(TK::Semicolon))) {
      recordGrammarFallback("invalid Annex A coverage spec header");
      recoverMalformedItem(saved);
      return true;
    }
    beginGrammar({body_rule});
    const bool braced = at(TK::OpenBrace);
    consumeInto(line_);
    const AnnexState body_prefix = endGrammar(!braced);
    if (body_prefix.failed || body_prefix.interrupted ||
        !body_prefix.hasViableRule(body_rule)) {
      recordGrammarFallback("invalid Annex A coverage spec body");
      recoverMalformedItem(saved);
      return true;
    }
    addLine();
    if (braced) {
      if (body_rule == "bins_or_empty") {
        parseCoverpointBinsBodyRule();
      } else {
        parseDelimitedBody(TK::CloseBrace, "cross_body_item");
      }
    }
    return true;
  }

  // coverage_spec_or_option ::= { attribute_instance } coverage_spec |
  //                              { attribute_instance } coverage_option ';'.
  auto parseCoverageSpecOrOptionRule() -> bool {
    if (at(TK::OpenParenthesis) && at(TK::Star, 1)) {
      const LeafCheckpoint saved = leafCheckpoint();
      bool valid = true;
      do {  // NOLINT(cppcoreguidelines-avoid-do-while)
        valid = consumeAnnexRule("attribute_instance", line_);
        parseGrammarChildDirectiveLines();
      } while (valid && at(TK::OpenParenthesis) && at(TK::Star, 1));
      if (valid && parseAttributeMacroInterruptionRule()) {
        return true;
      }
      if (valid && parseCoverageSpecOrOptionRule()) {
        return true;
      }
      recordGrammarFallback("invalid Annex A attributed coverage item");
      recoverMalformedItem(saved);
      return true;
    }
    return parseCoverageOptionRule() || parseCoverageSpecRule();
  }

  auto parseCaseItem() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    const std::string_view item_rule = block_stack_.back().grammar_body;
    const bool default_item = at(TK::DefaultKeyword);
    bool colon_seen = false;
    bool conditional_header = false;
    for (size_t i = pos_; i < tokens_.size(); ++i) {
      const TK kind = tokens_[i].kind;
      if (kind == TK::Colon || kind == TK::Semicolon ||
          kind == TK::EndCaseKeyword || kind == TK::EndOfFile) {
        break;
      }
      if (isConditionalStartDirective(tokens_[i])) {
        conditional_header = true;
        break;
      }
    }
    if (conditional_header) {
      beginGrammar({item_rule});
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
          if (at(TK::Directive)) {
            break;
          }
          consumeInto(line_);
        }
        if (at(TK::Colon)) {
          consumeInto(line_);
          colon_seen = true;
        }
      }
      const AnnexState header = endGrammar(false);
      colon_seen |= header.consumedTerminalInRule(item_rule, TK::Colon);
      if ((!default_item && !colon_seen) || header.failed ||
          header.interrupted || !header.hasViableRule(item_rule)) {
        recordGrammarFallback("invalid Annex A case item header");
        recoverMalformedItem(saved);
        return;
      }
    } else {
      bool valid = true;
      if (default_item) {
        valid = item_rule != "randcase_item";
        consumeInto(line_);
      } else if (item_rule == "case_item") {
        valid = consumeAnnexRule("case_item_expression", line_, TK::Colon);
        parseGrammarChildDirectiveLines();
        while (valid && at(TK::Comma)) {
          consumeInto(line_);
          parseGrammarChildDirectiveLines();
          valid = consumeAnnexRule("case_item_expression", line_, TK::Colon);
          parseGrammarChildDirectiveLines();
        }
      } else if (item_rule == "case_pattern_item") {
        valid = consumeAnnexRule("pattern", line_, TK::Colon);
        parseGrammarChildDirectiveLines();
        if (valid && at(TK::TripleAnd)) {
          consumeInto(line_);
          parseGrammarChildDirectiveLines();
          valid = consumeAnnexRule("expression", line_, TK::Colon);
        }
      } else if (item_rule == "case_inside_item") {
        valid = parseRangeListRule(TK::Colon);
      } else if (item_rule == "randcase_item") {
        valid = consumeAnnexRule("expression", line_, TK::Colon);
      } else if (item_rule == "case_generate_item") {
        valid = consumeAnnexRule("constant_expression", line_, TK::Colon);
        parseGrammarChildDirectiveLines();
        while (valid && at(TK::Comma)) {
          consumeInto(line_);
          parseGrammarChildDirectiveLines();
          valid = consumeAnnexRule("constant_expression", line_, TK::Colon);
          parseGrammarChildDirectiveLines();
        }
      } else {
        valid = false;
      }
      while (isCompilerDirective(peek()) &&
             !isConditionalStartDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
      if (at(TK::Colon)) {
        consumeInto(line_);
        colon_seen = true;
      }
      if (!valid || (!default_item && !colon_seen)) {
        recordGrammarFallback("invalid Annex A case item header");
        recoverMalformedItem(saved);
        return;
      }
    }
    if (atEnclosingBoundary()) {
      recordGrammarFallback("missing Annex A case item body");
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
      if (atEnclosingBoundary()) {
        recordGrammarFallback("missing Annex A do body");
        recoverMalformedItem(saved);
        return;
      }
      addLine();
      parseIndentedStatement({"statement_or_null"});
      parseGrammarChildDirectiveLines();
      if (!at(TK::WhileKeyword)) {
        recordGrammarFallback("do statement requires Annex A while tail");
        return;
      }
      consumeInto(line_);
      parseGrammarChildDirectiveLines();
      if (!consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                                 "expression", line_)) {
        recoverMalformedItem(saved);
        return;
      }
      parseGrammarChildDirectiveLines();
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
    consumeInto(line_);
    parseGrammarChildDirectiveLines();
    if (loop_kind == TK::ForKeyword) {
      if (!consumeForHeader(line_, generate)) {
        recoverMalformedItem(saved);
        return;
      }
    } else if (loop_kind == TK::WhileKeyword ||
               loop_kind == TK::RepeatKeyword) {
      const bool expression = consumeAnnexDelimited(
          TK::OpenParenthesis, TK::CloseParenthesis, "expression", line_);
      if (!expression || line_.tokens.empty() ||
          line_.tokens.back().kind != TK::CloseParenthesis) {
        recordGrammarFallback("incomplete Annex A loop header");
        recoverMalformedItem(saved);
        return;
      }
    } else if (foreach) {
      if (!parseForeachHeaderRule()) {
        recordGrammarFallback("incomplete Annex A foreach header");
        recoverMalformedItem(saved);
        return;
      }
    }
    parseGrammarChildDirectiveLines();
    if (!generate && at(TK::At)) {
      parseProceduralTimingControlStatementRule(true);
      return;
    }
    if (atEnclosingBoundary()) {
      recordGrammarFallback("missing Annex A loop body");
      recoverMalformedItem(saved);
      return;
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
  if (output_index != tokens.size()) {
    preserved = false;
  }
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
