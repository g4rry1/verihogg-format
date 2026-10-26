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
  };

  std::vector<AnnexChart> charts;
  std::vector<uint16_t> roots;
  size_t total_items = 0;
  bool failed = false;
  bool interrupted = false;
  std::string_view failure_reason;

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
          for (const size_t index : parents) {
            const AnnexItem parent = origin.items[index];
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
    return terminal >= 0 && !failed &&
           charts.back().scanning.contains(terminal);
  }

  [[nodiscard]] auto checkpoint() const -> Checkpoint {
    return {charts.size(), total_items, !failed && !interrupted};
  }

  // An opaque item occupies one grammar nonterminal. Resume the enclosing
  // grammar after that item without treating its unknown tokens as terminals.
  [[nodiscard]] auto skipOpaqueItem(
      Checkpoint saved, const std::vector<uint16_t>& item_roots) -> bool {
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
    failure_reason = {};
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
        interrupted != other.interrupted) {
      return false;
    }
    if (failed || interrupted) return true;
    const auto& lhs = charts.back();
    const auto& rhs = other.charts.back();
    if (lhs.completed_roots != rhs.completed_roots ||
        lhs.scanning.size() != rhs.scanning.size()) {
      return false;
    }
    for (const auto& [terminal, items] : lhs.scanning) {
      if (!rhs.scanning.contains(terminal)) return false;
    }
    return true;
  }

  [[nodiscard]] auto complete() const -> bool {
    if (failed || charts.size() == 1) return false;
    for (const auto root : roots) {
      if (charts.back().completed_roots.contains(root)) return true;
    }
    return false;
  }

  [[nodiscard]] auto completed(std::string_view name) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed || charts.size() == 1) return false;
    return charts.back().completed_roots.contains(rule);
  }

  [[nodiscard]] auto completedFrom(std::string_view name,
                                   size_t origin) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed) return false;
    const auto found = charts.back().completed_origins.find(rule);
    return found != charts.back().completed_origins.end() &&
           std::find(found->second.begin(), found->second.end(), origin) !=
               found->second.end();
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
    return false;
  }

  [[nodiscard]] auto hasViableRule(std::string_view name) const -> bool {
    const int rule = annexRule(name);
    if (rule < 0 || failed || charts.empty()) return false;
    return std::ranges::any_of(charts.back().items, [&](AnnexItem item) {
      return item.origin == 0 && kProductions[item.production].left == rule;
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
    return false;
  }

  auto advance(Token token) -> void {
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

    auto operator==(const BlockFrame&) const -> bool = default;
  };

  struct ParserState {
    size_t pos = 0;
    Line line;
    size_t indent_level = 0;
    std::vector<BlockFrame> block_stack;
    std::vector<AnnexState> grammar_scopes;
    std::vector<std::optional<AnnexState::Checkpoint>> grammar_checkpoints;
    std::vector<std::vector<std::string_view>> grammar_contexts;
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
  std::vector<std::vector<std::string_view>> grammar_contexts_;
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
      for (auto& scope : grammar_scopes_) {
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

  auto consumeBalancedInto(TK open, TK close, Line& line) -> void {
    if (!at(open)) {
      return;
    }
    consumeInto(line);
    int depth = 1;
    while (pos_ < tokens_.size() && !at(TK::EndOfFile) && depth > 0) {
      if (at(open)) {
        ++depth;
      } else if (at(close)) {
        --depth;
      }
      consumeInto(line);
    }
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
                         std::initializer_list<std::string_view> grammar_rules,
                         Line& line) -> void {
    beginGrammar(std::vector<std::string_view>(grammar_rules));
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
      return;
    }
    static_cast<void>(endGrammar());
  }

  auto consumeForHeader(Line& line) -> void {
    if (!at(TK::OpenParenthesis)) return;
    consumeInto(line);
    if (!at(TK::Semicolon)) {
      consumeAnnexUntil(TK::Semicolon, TK::CloseParenthesis,
                        {"for_initialization", "genvar_initialization"}, line);
    }
    if (at(TK::Semicolon)) consumeInto(line);
    if (!at(TK::Semicolon) && !at(TK::CloseParenthesis)) {
      consumeAnnexUntil(TK::Semicolon, TK::CloseParenthesis,
                        {"expression", "genvar_expression"}, line);
    }
    if (at(TK::Semicolon)) consumeInto(line);
    if (!at(TK::CloseParenthesis)) {
      consumeAnnexUntil(TK::CloseParenthesis, TK::EndOfFile,
                        {"for_step", "genvar_iteration"}, line);
    }
    if (at(TK::CloseParenthesis)) consumeInto(line);
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
      if (auto nested = blockSpec(tokens_[i].kind)) {
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
      if (auto block = blockSpec(kind)) {
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

  auto parseGrammarLeaf(bool recover_to_outer = false,
                        std::optional<LeafCheckpoint> checkpoint = {}) -> void {
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
        addLine();
        return;
      }
      if (at(TK::MacroUsage) ||
          (at(TK::Directive) && !isCompilerDirective(peek()))) {
        consumeInto(line_);
        consumeUntilSemi();
        return;
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
      addLine();
      return;
    }
    if (!recover_to_outer) {
      recordGrammarFallback("malformed Annex A item");
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
    if (at(TK::Colon)) {
      consumeInto(line_);
      if (!at(TK::EndOfFile)) {
        consumeInto(line_);
      }
    }
  }

  [[nodiscard]] auto looksLikePropertyAssertion(size_t offset = 0) const
      -> bool {
    return at(TK::AssertKeyword, offset) && at(TK::PropertyKeyword, offset + 1);
  }

  [[nodiscard]] auto looksLikeSupportedLabeledStatement() const -> bool {
    if (!at(TK::Identifier) || !at(TK::Colon, 1)) {
      return false;
    }

    if (looksLikePropertyAssertion(2)) {
      return true;
    }

    switch (peek(2).kind) {
      case TK::BeginKeyword:
      case TK::IfKeyword:
      case TK::CaseKeyword:
      case TK::CaseXKeyword:
      case TK::CaseZKeyword:
      case TK::ForKeyword:
      case TK::ForeachKeyword:
      case TK::WhileKeyword:
      case TK::RepeatKeyword:
      case TK::ForeverKeyword:
        return true;
      default:
        return false;
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
    grammar_contexts_ = state.grammar_contexts;
  }

  [[nodiscard]] auto structuralStateCompatible(
      const ParserState& lhs, const ParserState& rhs) const -> bool {
    if (lhs.indent_level != rhs.indent_level ||
        lhs.block_stack != rhs.block_stack ||
        lhs.grammar_contexts != rhs.grammar_contexts ||
        lhs.grammar_scopes.size() != rhs.grammar_scopes.size() ||
        lhs.grammar_checkpoints.size() != rhs.grammar_checkpoints.size()) {
      return false;
    }
    for (size_t i = 0; i < lhs.grammar_scopes.size(); ++i) {
      if (!lhs.grammar_scopes[i].sameContinuation(rhs.grammar_scopes[i])) {
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

  auto parseDelimitedBody(TK closeKind,
                          std::string_view bodyRule = {}) -> void {
    pushOpenFrame(closeKind);
    block_stack_.back().grammar_body = bodyRule;
    ++indent_level_;
    parseLevel(closeKind);
    if (matchesBlockClose(closeKind, peek().kind)) {
      parseOpenFrameClose();
    } else if (!(stop_at_conditional_boundary_ &&
                 isConditionalBoundaryDirective(peek()))) {
      recordGrammarFallback("incomplete block before outer boundary");
    }
  }

  auto parseIndentedStatement() -> void {
    const size_t stack_size_before = block_stack_.size();
    ++indent_level_;
    grammar_contexts_.push_back(
        {"statement_or_null", "generate_block", "generate_item"});
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
    if (!grammar_contexts_.empty()) return grammar_contexts_.back();
    if (block_stack_.empty()) {
      return {"description", "timeunits_declaration", "library_description"};
    }
    if (!block_stack_.back().grammar_body.empty()) {
      return {block_stack_.back().grammar_body};
    }
    switch (block_stack_.back().close_kind) {
      case TK::EndModuleKeyword:
        return {"module_item", "statement_or_null"};
      case TK::EndInterfaceKeyword:
        return {"interface_item", "statement_or_null"};
      case TK::EndProgramKeyword:
        return {"program_item", "statement_or_null"};
      case TK::EndPackageKeyword:
        return {"package_item"};
      case TK::EndClassKeyword:
        return {"class_item"};
      case TK::EndGenerateKeyword:
        return {"generate_item"};
      case TK::EndFunctionKeyword:
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
        return {"block_item_declaration", "statement_or_null"};
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
    grammar_scopes_.pop_back();
    const auto checkpoint = grammar_checkpoints_.back();
    grammar_checkpoints_.pop_back();
    if (checkpoint && !grammar_scopes_.empty() &&
        (state.failed || state.interrupted)) {
      static_cast<void>(
          grammar_scopes_.back().skipOpaqueItem(*checkpoint, state.roots));
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
      const bool structural_region =
          block_stack_.empty() ||
          (grammar_contexts_.empty() &&
           (block_stack_.back().close_kind == TK::EndModuleKeyword ||
            block_stack_.back().close_kind == TK::EndInterfaceKeyword ||
            block_stack_.back().close_kind == TK::EndProgramKeyword ||
            block_stack_.back().close_kind == TK::EndPackageKeyword ||
            block_stack_.back().close_kind == TK::EndGenerateKeyword));
      if (isConditionalStartDirective(peek()) && structural_region) {
        parseConditionalRegion();
      } else {
        parseDirectiveLine();
      }
      return;
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

    // A block header owns its Annex A state while it is consumed, and its
    // body is parsed item by item. All other items keep a chart active through
    // the same consume() calls that emit their UnwrappedLine tokens.
    const auto block = blockSpec(peek().kind);
    const bool virtual_class = at(TK::VirtualKeyword) &&
                               annexCanStart("class_declaration", peek().kind);
    const bool prefixed_clocking =
        (at(TK::DefaultKeyword) || at(TK::GlobalKeyword)) &&
        at(TK::ClockingKeyword, 1);
    const bool constraint_block =
        at(TK::ConstraintKeyword) ||
        (at(TK::StaticKeyword) && at(TK::ConstraintKeyword, 1));
    const bool own_grammar =
        !virtual_class && !prefixed_clocking && !constraint_block &&
        (!block || (block->layout != BlockLayout::Structural &&
                    block->layout != BlockLayout::Named &&
                    block->layout != BlockLayout::DelimitedRecovery));
    if (own_grammar) beginGrammar(grammarRoots(), true);
    parseStatementLayout();
    if (own_grammar) {
      const AnnexState item = endGrammar();
      if (!block_stack_.empty() &&
          (block_stack_.back().close_kind == TK::EndFunctionKeyword ||
           block_stack_.back().close_kind == TK::EndTaskKeyword) &&
          !item.completed("tf_item_declaration") &&
          !item.completed("block_item_declaration")) {
        block_stack_.back().statement_phase = true;
      }
    }
  }

  auto parseStatementLayout() -> void {
    // Annex A puts unique / unique0 / priority before both if and case.
    // Finish that grammar prefix before selecting the layout function.
    if (!grammar_scopes_.empty() &&
        annexCanStart("unique_priority", peek().kind) &&
        grammarAllows(peek().kind)) {
      const size_t origin = grammar_scopes_.back().charts.size() - 1;
      consumeInto(line_);
      if (!grammar_scopes_.back().completedFrom("unique_priority", origin)) {
        recordGrammarFallback("incomplete Annex A unique_priority");
        grammar_scopes_.back().interrupted = true;
        consumeUntilSemi();
        return;
      }
    }
    const TK first = peek().kind;
    const auto starts = [&](std::string_view rule) {
      return annexCanStart(rule, first);
    };
    const auto allowed_here = [&] {
      const auto roots = grammarRoots();
      return std::ranges::any_of(roots, [&](std::string_view rule) {
        return annexCanStart(rule, first);
      });
    };

    // These declarations use Annex A for their header and for each repeated
    // body item. The chart advances in consume(), alongside line emission.
    if ((first == TK::ConstraintKeyword ||
         (first == TK::StaticKeyword && at(TK::ConstraintKeyword, 1))) &&
        (starts("constraint_declaration") ||
         starts("extern_constraint_declaration")) &&
        allowed_here()) {
      parseConstraintBlock();
      return;
    }
    if (first == TK::CoverGroupKeyword && starts("covergroup_declaration") &&
        allowed_here()) {
      parseAnnexDelimitedBlock(TK::EndGroupKeyword, "covergroup_declaration",
                               "coverage_spec_or_option");
      return;
    }
    if (first == TK::CheckerKeyword && starts("checker_declaration") &&
        allowed_here()) {
      parseAnnexDelimitedBlock(TK::EndCheckerKeyword, "checker_declaration",
                               "checker_or_generate_item");
      return;
    }
    if ((first == TK::ClockingKeyword ||
         ((first == TK::DefaultKeyword || first == TK::GlobalKeyword) &&
          at(TK::ClockingKeyword, 1))) &&
        starts("clocking_declaration") && allowed_here()) {
      parseAnnexDelimitedBlock(TK::EndClockingKeyword, "clocking_declaration",
                               "clocking_item");
      return;
    }
    if (first == TK::SpecifyKeyword && starts("specify_block") &&
        allowed_here()) {
      parseAnnexDelimitedBlock(TK::EndSpecifyKeyword, "specify_block",
                               "specify_item", false);
      return;
    }
    if (first == TK::PropertyKeyword && starts("property_declaration") &&
        allowed_here()) {
      parseAnnexWholeBlock(TK::EndPropertyKeyword, "property_declaration");
      return;
    }
    if (first == TK::SequenceKeyword && starts("sequence_declaration") &&
        allowed_here()) {
      parseAnnexWholeBlock(TK::EndSequenceKeyword, "sequence_declaration");
      return;
    }
    if (first == TK::ConfigKeyword && starts("config_declaration") &&
        allowed_here()) {
      parseConfigBlock();
      return;
    }
    if (first == TK::PrimitiveKeyword && starts("udp_declaration") &&
        allowed_here()) {
      parsePrimitiveBlock();
      return;
    }
    // A table only occurs inside udp_body. A standalone table has no Annex A
    // production and retains the enclosing-close recovery path.
    if (const auto block = blockSpec(first);
        block && block->layout == BlockLayout::DelimitedRecovery) {
      parseOpaqueBlock(block->close_kind);
      return;
    }
    if (looksLikeSupportedLabeledStatement()) {
      parseLabeledStatement();
      return;
    }
    if (!block_stack_.empty() &&
        (block_stack_.back().grammar_body == "coverage_spec_or_option" ||
         block_stack_.back().grammar_body == "clocking_item" ||
         block_stack_.back().grammar_body == "specify_item") &&
        grammarAllows(first)) {
      parseGrammarLeaf();
      return;
    }

    // Annex A FIRST sets select the construction family. These calls control
    // only line layout; the active chart continues to decide membership and
    // completion as each token is consumed.
    if (starts("module_ansi_header") || starts("module_nonansi_header")) {
      parseStructuralBlock(TK::EndModuleKeyword);
    } else if (starts("interface_class_declaration") &&
               at(TK::ClassKeyword, 1)) {
      parseNamedBlock(TK::EndClassKeyword);
    } else if (starts("interface_ansi_header") ||
               starts("interface_nonansi_header")) {
      parseStructuralBlock(TK::EndInterfaceKeyword);
    } else if (starts("program_ansi_header") ||
               starts("program_nonansi_header")) {
      parseStructuralBlock(TK::EndProgramKeyword);
    } else if (starts("package_declaration")) {
      parseStructuralBlock(TK::EndPackageKeyword);
    } else if (starts("class_declaration")) {
      parseNamedBlock(TK::EndClassKeyword);
    } else if (starts("function_declaration")) {
      parseNamedBlock(TK::EndFunctionKeyword);
    } else if (starts("task_declaration")) {
      parseNamedBlock(TK::EndTaskKeyword);
    } else if (starts("generate_region")) {
      parseSimpleBlock(TK::EndGenerateKeyword);
    } else if (starts("seq_block")) {
      parseBeginEnd(TK::EndKeyword);
    } else if (starts("par_block")) {
      parseFork(TK::JoinKeyword);
    } else if (starts("case_statement") || starts("case_generate_construct")) {
      parseCase(TK::EndCaseKeyword);
    } else if (starts("always_construct") || starts("initial_construct") ||
               starts("final_construct")) {
      parseProceduralBlock();
    } else if (starts("conditional_statement") ||
               starts("if_generate_construct")) {
      parseIf();
    } else if (starts("loop_statement") || starts("loop_generate_construct")) {
      parseLoop();
    } else if (starts("assert_property_statement") &&
               looksLikePropertyAssertion()) {
      parseAssertionStatement();
    } else if (first == TK::Identifier) {
      parseIdentifierItem();
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

  auto parseLabeledStatement() -> void {
    consumeInto(line_);  // label identifier
    consumeInto(line_);  // colon
    parseStatement();
  }

  auto parseAssertionStatement() -> void {
    consumeInto(line_);  // assert
    consumeInto(line_);  // property
    consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                          "property_spec", line_);

    if (at(TK::Semicolon)) {
      consumeInto(line_);
      addLine();
      return;
    }

    if (at(TK::EndOfFile) || (stop_at_conditional_boundary_ &&
                              isConditionalBoundaryDirective(peek()))) {
      addLine();
      return;
    }

    if (!at(TK::ElseKeyword) && !at(TK::EndOfFile)) {
      grammar_contexts_.push_back({"statement_or_null"});
      parseStatement();
      grammar_contexts_.pop_back();
    }

    if (at(TK::ElseKeyword) && grammarAllows(TK::ElseKeyword)) {
      consumeInto(line_);
      if (at(TK::EndOfFile)) {
        addLine();
        return;
      }
      grammar_contexts_.push_back({"statement_or_null"});
      parseStatement();
      grammar_contexts_.pop_back();
    }
  }

  // Identifier-led items can become declarations, assignments or
  // instantiations. Consume the common prefix once; list layout starts only
  // when the next consumed tokens actually open a parameter or port list.
  auto parseIdentifierItem() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    consumeInto(line_);
    while (at(TK::Directive) && isCompilerDirective(peek())) {
      addLine();
      parseDirectiveLine();
    }
    if (at(TK::Hash)) {
      consumeInto(line_);
      parseParenthesizedListInto(line_);
      while (at(TK::Directive) && isCompilerDirective(peek())) {
        addLine();
        parseDirectiveLine();
      }
    }
    if (at(TK::Identifier)) {
      consumeInto(line_);
      if (at(TK::OpenParenthesis)) {
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
  auto parseParenthesizedListInto(Line& line) -> void {
    if (!at(TK::OpenParenthesis)) {
      return;
    }
    line.tokens.push_back(consume());

    addLine();
    int parenDepth = 0;
    int bracketDepth = 0;
    int braceDepth = 0;

    auto atTopLevel = [&]() -> bool {
      return parenDepth == 0 && bracketDepth == 0 && braceDepth == 0;
    };

    while (!at(TK::EndOfFile)) {
      if (at(TK::CloseParenthesis) && atTopLevel()) {
        break;
      }

      if (atTopLevel() && isCompilerDirective(peek()) &&
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

      if (at(TK::Comma) && atTopLevel()) {
        consumeInto(line);
        addLine();
        continue;
      }

      switch (peek().kind) {
        case TK::OpenParenthesis:
          ++parenDepth;
          break;
        case TK::CloseParenthesis:
          if (parenDepth > 0) {
            --parenDepth;
          }
          break;
        case TK::OpenBracket:
          ++bracketDepth;
          break;
        case TK::CloseBracket:
          if (bracketDepth > 0) {
            --bracketDepth;
          }
          break;
        case TK::ApostropheOpenBrace:
        case TK::OpenBrace:
          ++braceDepth;
          break;
        case TK::CloseBrace:
          if (braceDepth > 0) {
            --braceDepth;
          }
          break;
        default:
          break;
      }
      consumeInto(line);
    }
    addLine();
    if (at(TK::CloseParenthesis)) {
      line.tokens.push_back(consume());
    }
  }

  // module foo #(...) (...); ... endmodule
  auto consumeGrammarHeader(
      TK closeKw, std::initializer_list<std::string_view> boundaryRules,
      std::initializer_list<std::string_view> completedRules = {}) -> void {
    while (!at(TK::EndOfFile) && !at(closeKw) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
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
                                    size_t baseIndent) -> bool {
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
    if (kind == closeKw) {
      addLine();
      if (indent_level_ > baseIndent) --indent_level_;
    }
    consumeInto(line_);
    if (kind == TK::Semicolon) {
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
  auto parseAnnexConditional(TK closeKw, bool& headerEnded,
                             size_t baseIndent) -> bool {
    addLine();
    parseDirectiveLine();  // ifdef / ifndef
    const auto entry = grammar_scopes_;
    const bool entry_header_ended = headerEnded;
    const size_t entry_indent = indent_level_;
    struct Continuation {
      std::vector<AnnexState> grammars;
      bool header_ended;
      size_t indent;
    };
    std::vector<Continuation> branches;
    bool has_else = false;
    while (!at(TK::EndOfFile)) {
      grammar_scopes_ = entry;
      headerEnded = entry_header_ended;
      indent_level_ = entry_indent;
      while (!at(TK::EndOfFile) && !isConditionalBoundaryDirective(peek())) {
        if (isConditionalStartDirective(peek())) {
          if (!parseAnnexConditional(closeKw, headerEnded, baseIndent)) {
            return false;
          }
        } else if (isCompilerDirective(peek())) {
          addLine();
          parseDirectiveLine();
        } else if (!consumeAnnexConditionalToken(closeKw, headerEnded,
                                                 baseIndent)) {
          return false;
        }
      }
      addLine();
      branches.push_back({grammar_scopes_, headerEnded, indent_level_});
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
      branches.push_back({entry, entry_header_ended, entry_indent});
    }
    if (branches.empty()) return false;
    const auto& joined = branches.front();
    for (const auto& branch : branches) {
      bool same_grammar = joined.grammars.size() == branch.grammars.size();
      for (size_t i = 0; same_grammar && i < joined.grammars.size(); ++i) {
        same_grammar = joined.grammars[i].sameContinuation(branch.grammars[i]);
      }
      if (!same_grammar || joined.header_ended != branch.header_ended ||
          joined.indent != branch.indent) {
        recordGrammarFallback("incompatible conditional Annex A branches");
        return false;
      }
    }
    grammar_scopes_ = joined.grammars;
    headerEnded = joined.header_ended;
    indent_level_ = joined.indent;
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

  auto parseAnnexItem(std::vector<std::string_view> rules) -> AnnexState {
    beginGrammar(std::move(rules));
    parseGrammarLeaf();
    return endGrammar();
  }

  auto parseConstraintBlock() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    beginGrammar({"constraint_declaration", "extern_constraint_declaration"});
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
    ++indent_level_;
    while (!at(TK::CloseBrace) && !at(TK::EndOfFile) && !at(outer_close) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
      if (at(TK::Directive)) {
        parseStatement();
      } else {
        static_cast<void>(parseAnnexItem({"constraint_block_item"}));
      }
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
    ++indent_level_;

    // config_declaration prescribes zero or more local parameters, exactly
    // one design_statement, then zero or more config_rule_statement items.
    while (annexCanStart("local_parameter_declaration", peek().kind) ||
           isCompilerDirective(peek())) {
      if (isCompilerDirective(peek())) {
        parseDirectiveLine();
        continue;
      }
      beginGrammar({"local_parameter_declaration"});
      while (!at(TK::Semicolon) && !at(TK::EndOfFile) &&
             !matchingOpenFrame(peek().kind) &&
             grammar_scopes_.back().accepts(peek().kind)) {
        consumeInto(line_);
      }
      const bool complete = grammar_scopes_.back().complete();
      static_cast<void>(endGrammar());
      if (!complete || !at(TK::Semicolon)) {
        recordGrammarFallback("malformed config local parameter");
        consumeUntilSemi();
      } else {
        consumeInto(line_);
        addLine();
      }
    }
    if (annexCanStart("design_statement", peek().kind)) {
      static_cast<void>(parseAnnexItem({"design_statement"}));
    } else {
      recordGrammarFallback("config requires design_statement");
    }
    while (!at(TK::EndConfigKeyword) && !at(TK::EndOfFile) &&
           !(stop_at_conditional_boundary_ &&
             isConditionalBoundaryDirective(peek()))) {
      if (at(TK::Directive)) {
        parseStatement();
      } else {
        static_cast<void>(parseAnnexItem({"config_rule_statement"}));
      }
    }
    if (at(TK::EndConfigKeyword)) {
      parseOpenFrameClose();
    } else {
      recordGrammarFallback("incomplete config declaration");
    }
  }

  auto parsePrimitiveBlock() -> void {
    beginGrammar({"udp_declaration"});
    consumeGrammarHeader(TK::EndPrimitiveKeyword, {},
                         {"udp_nonansi_declaration", "udp_ansi_declaration"});
    const AnnexState header = endGrammar(false);
    const bool nonansi = header.completedFrom("udp_nonansi_declaration", 0);
    const bool ansi = header.completedFrom("udp_ansi_declaration", 0);
    pushOpenFrame(TK::EndPrimitiveKeyword);
    ++indent_level_;

    size_t port_declarations = 0;
    while (annexCanStart("udp_port_declaration", peek().kind) ||
           isCompilerDirective(peek())) {
      if (isCompilerDirective(peek())) {
        parseDirectiveLine();
      } else {
        static_cast<void>(parseAnnexItem({"udp_port_declaration"}));
        ++port_declarations;
      }
    }
    if ((nonansi && port_declarations == 0) ||
        (ansi && port_declarations != 0)) {
      recordGrammarFallback("UDP port declarations do not match header");
    }
    bool sequential = false;
    bool combinational = false;
    if (annexCanStart("udp_initial_statement", peek().kind)) {
      static_cast<void>(parseAnnexItem({"udp_initial_statement"}));
      sequential = true;
    }
    if (annexCanStart("combinational_body", peek().kind) ||
        annexCanStart("sequential_body", peek().kind)) {
      consumeInto(line_);
      addLine();
      pushOpenFrame(TK::EndTableKeyword);
      ++indent_level_;
      size_t entry_count = 0;
      while (!at(TK::EndTableKeyword) && !at(TK::EndPrimitiveKeyword) &&
             !at(TK::EndOfFile) &&
             !(stop_at_conditional_boundary_ &&
               isConditionalBoundaryDirective(peek()))) {
        if (at(TK::Directive)) {
          parseStatement();
        } else {
          std::vector<std::string_view> roots;
          if (!sequential) roots.push_back("combinational_entry");
          if (!combinational) roots.push_back("sequential_entry");
          const AnnexState entry = parseAnnexItem(std::move(roots));
          combinational |= entry.completed("combinational_entry");
          sequential |= entry.completed("sequential_entry");
          ++entry_count;
        }
      }
      if (entry_count == 0) {
        recordGrammarFallback("UDP table requires an entry");
      }
      if (at(TK::EndTableKeyword)) {
        parseOpenFrameClose();
      } else {
        recordGrammarFallback("incomplete UDP table");
        block_stack_.pop_back();
        if (indent_level_ > 0) --indent_level_;
      }
    } else {
      recordGrammarFallback("UDP declaration requires udp_body");
      if (!at(TK::EndPrimitiveKeyword)) {
        emitOpaque(pos_, findOuterBoundary(pos_));
      }
    }
    if (at(TK::EndPrimitiveKeyword)) {
      parseOpenFrameClose();
    } else if (!(stop_at_conditional_boundary_ &&
                 isConditionalBoundaryDirective(peek()))) {
      recordGrammarFallback("incomplete UDP declaration");
    }
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
        if (isCompilerDirective(peek())) {
          addLine();
          parseDirectiveLine();
          continue;
        }
        if (!grammar_scopes_.back().accepts(peek().kind)) break;
        if (at(TK::Hash)) {
          consumeInto(line_);
          consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
        } else if (at(TK::OpenParenthesis)) {
          // Port lists are layout choices over the same grammar consumption.
          parseParenthesizedListInto(line_);
        } else {
          consumeInto(line_);
        }
      }
      if (grammar_scopes_.back().interrupted || grammar_scopes_.back().failed) {
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
        header.completed("module_ansi_header")) {
      body_rule = "non_port_module_item";
    } else if (closeKw == TK::EndInterfaceKeyword &&
               header.completed("interface_ansi_header")) {
      body_rule = "non_port_interface_item";
    } else if (closeKw == TK::EndProgramKeyword &&
               header.completed("program_ansi_header")) {
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
    consumeInto(line_);
    addLine();

    parseDelimitedBody(closeKw);
  }

  // begin [:label] ... end [:label]
  auto parseBeginEnd(TK closeKw) -> void {
    consumeInto(line_);  // begin
    consumeLabel();
    addLine();

    parseDelimitedBody(closeKw);
  }

  // fork ... join / join_any / join_none
  auto parseFork(TK closeKw) -> void {
    consumeInto(line_);
    consumeLabel();
    addLine();
    parseDelimitedBody(closeKw);
  }

  // always / always_comb / always_ff / always_latch / initial / final
  auto parseProceduralBlock() -> void {
    const LeafCheckpoint saved = leafCheckpoint();
    const auto recover_control = [&] {
      if (!recovery_enabled_) {
        consumeUntilSemi();
        return;
      }
      lines_.resize(saved.output_size);
      line_ = saved.line;
      preserved_source_end_ = saved.preserved_source_end;
      indent_level_ = saved.indent_level;
      emitOpaque(saved.pos, findOuterBoundary(saved.pos));
    };
    consumeInto(line_);  // keyword
    bool has_delay_control = false;
    if (at(TK::Hash)) {
      has_delay_control = true;
      if (!consumeAnnexRule("delay_control", line_)) {
        recover_control();
        return;
      }
    }
    if (at(TK::At)) {
      if (!consumeAnnexRule("event_control", line_)) {
        recover_control();
        return;
      }
    }
    const TK next = peek().kind;
    const bool compound_statement =
        annexCanStart("seq_block", next) || annexCanStart("par_block", next) ||
        annexCanStart("conditional_statement", next) ||
        annexCanStart("case_statement", next) ||
        annexCanStart("loop_statement", next);
    if (has_delay_control && !compound_statement) {
      parseGrammarLeaf();
      return;
    }
    addLine();

    parseIndentedStatement();
  }

  // if (...) stmt [else [if (...)] stmt]
  auto parseIf() -> void {
    consumeInto(line_);  // if
    consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                          "cond_predicate", line_);
    addLine();

    parseIndentedStatement();

    if (at(TK::ElseKeyword) && grammarAllows(TK::ElseKeyword)) {
      consumeInto(line_);  // else
      if (at(TK::IfKeyword)) {
        // else if: `if (...)` is added into the same line_ that already has
        // `else`
        parseIf();
        return;
      }
      addLine();
      parseIndentedStatement();
    }
  }

  // case/casex/casez (...) ... endcase
  auto parseCase(TK closeKw) -> void {
    consumeInto(line_);  // case / casex / casez
    consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                          "case_expression", line_);
    if ((at(TK::InsideKeyword) || at(TK::MatchesKeyword)) &&
        grammarAllows(peek().kind)) {
      consumeInto(line_);
    }
    addLine();

    pushOpenFrame(closeKw);
    ++indent_level_;
    while (!at(closeKw) && !at(TK::EndOfFile)) {
      if (stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(peek())) {
        return;
      }
      if (at(TK::Directive)) {
        if (isCompilerDirective(peek())) {
          parseDirectiveLine();
        } else {
          parseStatement();
        }
      } else {
        parseCaseItem();
      }
    }

    if (at(closeKw)) {
      parseOpenFrameClose();
    }
  }

  auto parseCaseItem() -> void {
    beginGrammar({"case_item", "case_pattern_item", "case_inside_item",
                  "case_generate_item"},
                 true);
    if (at(TK::DefaultKeyword)) {
      consumeInto(line_);
      if (at(TK::Colon)) {
        consumeInto(line_);
      }
    } else {
      while (!at(TK::Directive) && !at(TK::EndOfFile) &&
             !at(TK::EndCaseKeyword) &&
             !(at(TK::Colon) &&
               (grammar_scopes_.back().failed ||
                grammar_scopes_.back().expectsRootTerminal(TK::Colon)))) {
        consumeInto(line_);
      }
      if (at(TK::Colon)) {
        consumeInto(line_);
      }
    }
    addLine();

    parseIndentedStatement();
    static_cast<void>(endGrammar());
  }

  // for / foreach / while / repeat / forever
  auto parseLoop() -> void {
    if (at(TK::DoKeyword)) {
      consumeInto(line_);
      addLine();
      parseIndentedStatement();
      if (at(TK::WhileKeyword) && grammarAllows(TK::WhileKeyword)) {
        consumeInto(line_);
        consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                              "expression", line_);
        if (at(TK::Semicolon) && grammarAllows(TK::Semicolon)) {
          consumeInto(line_);
        }
        addLine();
      }
      return;
    }
    const TK loop_kind = peek().kind;
    consumeInto(line_);  // keyword
    if (at(TK::OpenParenthesis)) {
      if (loop_kind == TK::ForKeyword) {
        consumeForHeader(line_);
      } else if (loop_kind == TK::WhileKeyword ||
                 loop_kind == TK::RepeatKeyword) {
        consumeAnnexDelimited(TK::OpenParenthesis, TK::CloseParenthesis,
                              "expression", line_);
      } else {
        consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
      }
    }
    if (at(TK::At)) {
      consumeInto(line_);
      consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
      if (at(TK::BeginKeyword)) {
        consumeInto(line_);
        consumeLabel();
        addLine();
        parseDelimitedBody(TK::EndKeyword);
        return;
      }
    }
    addLine();

    parseIndentedStatement();
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
