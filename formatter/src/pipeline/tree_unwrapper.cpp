#include "pipeline/tree_unwrapper.h"

#include <slang/parsing/LexerFacts.h>
#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

#include <functional>
#include <gsl/span>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "data/format_warning.h"
#include "data/unwrapped_line.h"

namespace format {

namespace {

using Token = slang::parsing::Token;
using TK = slang::parsing::TokenKind;
using TriviaKind = slang::parsing::TriviaKind;
using Line = UnwrappedLine<Token>;

[[nodiscard]] auto isCompilerDirective(Token tok) -> bool {
  if (tok.kind != TK::Directive) {
    return false;
  }

  const std::string_view text = tok.rawText();
  return text == "`begin_keywords" || text == "`celldefine" ||
         text == "`default_decay_time" || text == "`default_nettype" ||
         text == "`default_trireg_strength" || text == "`define" ||
         text == "`else" || text == "`elsif" || text == "`end_keywords" ||
         text == "`endcelldefine" || text == "`endif" ||
         text == "`endprotect" || text == "`endprotected" || text == "`ifdef" ||
         text == "`ifndef" || text == "`include" || text == "`line" ||
         text == "`nounconnected_drive" || text == "`pragma" ||
         text == "`protect" || text == "`protected" || text == "`resetall" ||
         text == "`timescale" || text == "`unconnected_drive" ||
         text == "`undef" || text == "`undefineall";
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
  SVParser(gsl::span<const Token> tokens, const FormatStyle& style)
      : tokens_(tokens), style_(style) {}

  auto parse() -> UnwrapResult {
    parseLevel(TK::EndOfFile);
    return {
        .lines = std::move(lines_),
        .warnings = std::move(warnings_),
    };
  }

 private:
  struct BlockFrame {
    TK close_kind;
    size_t extra_dedent_after_close = 0;

    auto operator==(const BlockFrame&) const -> bool = default;
  };

  struct ParserState {
    size_t pos = 0;
    Line line;
    size_t indent_level = 0;
    std::vector<BlockFrame> block_stack;
  };

  struct BranchResult {
    ParserState state;
    std::vector<Line> lines;
    std::vector<FormatWarning> warnings;
  };

  gsl::span<const Token> tokens_;
  std::reference_wrapper<const FormatStyle> style_;
  size_t pos_ = 0;
  Line line_;
  std::vector<Line> lines_;
  std::vector<FormatWarning> warnings_;
  size_t indent_level_ = 0;
  std::vector<BlockFrame> block_stack_;
  bool stop_at_conditional_boundary_ = false;

  // ---- token access ----

  [[nodiscard]] auto peek(size_t offset = 0) const -> Token {
    size_t idx = pos_ + offset;
    return (idx < tokens_.size()) ? tokens_[idx] : tokens_.back();
  }

  [[nodiscard]] auto at(TK kind, size_t offset = 0) const -> bool {
    return peek(offset).kind == kind;
  }

  auto consume() -> Token {
    return (pos_ < tokens_.size()) ? tokens_[pos_++] : tokens_.back();
  }

  auto consumeInto(Line& line) -> void { line.tokens.push_back(consume()); }

  // ---- line management ----

  auto addLine() -> void {
    if (line_.tokens.empty()) {
      return;
    }
    line_.indentation_spaces = indent_level_ * style_.get().indentation_spaces;
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
    while (pos_ < tokens_.size() && depth > 0) {
      if (at(open)) {
        ++depth;
      } else if (at(close)) {
        --depth;
      }
      consumeInto(line);
    }
  }

  auto consumeUntilSemi() -> void {
    while (pos_ < tokens_.size() && !at(TK::Semicolon) && !at(TK::EndOfFile)) {
      if (stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(peek())) {
        break;
      }
      if (isCompilerDirective(peek())) {
        addLine();
        if (isConditionalStartDirective(peek()) &&
            (stop_at_conditional_boundary_ || shouldParseConditionalRegion())) {
          parseConditionalRegion();
        } else {
          parseDirectiveLine();
        }
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
                   std::string(construct) + "'; formatted in fallback mode",
    });
  }

  [[nodiscard]] static auto unsupportedConstructName(Token tok)
      -> std::string_view {
    if (!tok.rawText().empty()) {
      return tok.rawText();
    }
    return "unknown";
  }

  auto parseUnsupportedConstruct() -> void {
    const Token start = peek();
    warnUnsupported(start, unsupportedConstructName(start));
    consumeUntilSemi();
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

  [[nodiscard]] auto skipBalancedLookahead(size_t& offset, TK open,
                                           TK close) const -> bool {
    if (!at(open, offset)) {
      return false;
    }

    int depth = 0;
    while (pos_ + offset < tokens_.size() && !at(TK::EndOfFile, offset)) {
      if (at(open, offset)) {
        ++depth;
      } else if (at(close, offset)) {
        --depth;
        ++offset;
        if (depth == 0) {
          return true;
        }
        continue;
      }
      ++offset;
    }
    return false;
  }

  [[nodiscard]] auto afterDirectiveLine(size_t index) const -> size_t {
    ++index;
    while (index < tokens_.size() && tokens_[index].kind != TK::EndOfFile) {
      if (hasLeadingNewline(tokens_[index])) {
        break;
      }
      ++index;
    }
    return index;
  }

  [[nodiscard]] auto looksLikeInstantiation() const -> bool {
    if (!at(TK::Identifier)) {
      return false;
    }

    size_t offset = 1;
    if (at(TK::Hash, offset)) {
      ++offset;
      if (!skipBalancedLookahead(offset, TK::OpenParenthesis,
                                 TK::CloseParenthesis)) {
        return false;
      }
    }

    return at(TK::Identifier, offset) && at(TK::OpenParenthesis, offset + 1);
  }

  [[nodiscard]] auto snapshotState() const -> ParserState {
    return {
        .pos = pos_,
        .line = line_,
        .indent_level = indent_level_,
        .block_stack = block_stack_,
    };
  }

  auto restoreState(const ParserState& state) -> void {
    pos_ = state.pos;
    line_ = state.line;
    indent_level_ = state.indent_level;
    block_stack_ = state.block_stack;
  }

  [[nodiscard]] auto structuralStateCompatible(
      const ParserState& lhs, const ParserState& rhs) const -> bool {
    return lhs.indent_level == rhs.indent_level &&
           lhs.block_stack == rhs.block_stack;
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

  [[nodiscard]] auto parseBranch(const ParserState& state) const -> BranchResult {
    SVParser branch(tokens_, style_.get());
    branch.restoreState(state);
    branch.lines_.clear();
    branch.warnings_.clear();
    branch.stop_at_conditional_boundary_ = true;
    branch.parseLevel(TK::EndOfFile);
    return {
        .state = branch.snapshotState(),
        .lines = std::move(branch.lines_),
        .warnings = std::move(branch.warnings_),
    };
  }

  [[nodiscard]] auto shouldParseConditionalRegion() const -> bool {
    if (!isConditionalStartDirective(peek())) {
      return false;
    }

    ParserState branch_entry = snapshotState();
    branch_entry.pos = afterDirectiveLine(pos_);
    branch_entry.line = Line{};

    std::vector<ParserState> branch_states;
    bool saw_alternative = false;
    bool saw_structural_change = false;

    while (branch_entry.pos < tokens_.size()) {
      ParserState branch_start = branch_entry;
      branch_start.line = Line{};

      BranchResult branch = parseBranch(branch_start);
      if (branch.state.pos >= tokens_.size() ||
          tokens_[branch.state.pos].kind == TK::EndOfFile) {
        return false;
      }

      if (!isConditionalBoundaryDirective(tokens_[branch.state.pos])) {
        return false;
      }

      saw_structural_change =
          saw_structural_change ||
          !structuralStateCompatible(branch_entry, branch.state);
      branch_states.push_back(branch.state);

      if (isConditionalAlternativeDirective(tokens_[branch.state.pos])) {
        saw_alternative = true;
        branch_entry.pos = afterDirectiveLine(branch.state.pos);
        branch_entry.line = Line{};
        continue;
      }

      if (isConditionalEndDirective(tokens_[branch.state.pos])) {
        if (!saw_alternative) {
          ParserState empty_branch = branch_entry;
          empty_branch.pos = branch.state.pos;
          empty_branch.line = Line{};
          branch_states.push_back(empty_branch);
        }
        return saw_structural_change && joinStates(branch_states).has_value();
      }

      return false;
    }

    return false;
  }

  auto appendBranchResult(BranchResult& branch) -> void {
    lines_.insert(lines_.end(), std::make_move_iterator(branch.lines.begin()),
                  std::make_move_iterator(branch.lines.end()));
    warnings_.insert(warnings_.end(),
                     std::make_move_iterator(branch.warnings.begin()),
                     std::make_move_iterator(branch.warnings.end()));
  }

  [[nodiscard]] auto matchingOpenFrame(TK kind) const -> bool {
    return !block_stack_.empty() && block_stack_.back().close_kind == kind;
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
    consumeLabel();
    addLine();
    indent_level_ = (indent_level_ >= frame.extra_dedent_after_close)
                        ? indent_level_ - frame.extra_dedent_after_close
                        : 0;
  }

  auto pushOpenFrame(TK closeKind) -> void {
    block_stack_.push_back(BlockFrame{.close_kind = closeKind});
  }

  auto parseIndentedStatement() -> void {
    const size_t stack_size_before = block_stack_.size();
    ++indent_level_;
    parseStatement();
    if (block_stack_.size() == stack_size_before) {
      --indent_level_;
    } else if (!block_stack_.empty()) {
      ++block_stack_.back().extra_dedent_after_close;
    }
  }

  // ---- grammar ----

  // NOLINTBEGIN(misc-no-recursion)

  auto parseLevel(TK stopKind) -> void {
    while (pos_ < tokens_.size()) {
      auto kind = peek().kind;
      if (kind == stopKind || kind == TK::EndOfFile) {
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

    // Module/interface instantiations are identifier-led, so they cannot be
    // dispatched by TokenKind in the switch below.
    if (looksLikeInstantiation()) {
      parseInstantiation();
      return;
    }

    switch (peek().kind) {
      case TK::ModuleKeyword:
      case TK::MacromoduleKeyword:
        parseStructuralBlock(TK::EndModuleKeyword);
        break;
      case TK::InterfaceKeyword:
        parseStructuralBlock(TK::EndInterfaceKeyword);
        break;
      case TK::PackageKeyword:
        parseStructuralBlock(TK::EndPackageKeyword);
        break;
      case TK::ProgramKeyword:
        parseStructuralBlock(TK::EndProgramKeyword);
        break;

      case TK::ClassKeyword:
        parseNamedBlock(TK::EndClassKeyword);
        break;
      case TK::FunctionKeyword:
        parseNamedBlock(TK::EndFunctionKeyword);
        break;
      case TK::TaskKeyword:
        parseNamedBlock(TK::EndTaskKeyword);
        break;

      case TK::GenerateKeyword:
        parseSimpleBlock(TK::EndGenerateKeyword);
        break;

      case TK::BeginKeyword:
        parseBeginEnd();
        break;
      case TK::ForkKeyword:
        parseFork();
        break;

      case TK::AlwaysKeyword:
      case TK::AlwaysCombKeyword:
      case TK::AlwaysFFKeyword:
      case TK::AlwaysLatchKeyword:
      case TK::InitialKeyword:
      case TK::FinalKeyword:
        parseProceduralBlock();
        break;

      case TK::IfKeyword:
        parseIf();
        break;

      case TK::CaseKeyword:
      case TK::CaseXKeyword:
      case TK::CaseZKeyword:
        parseCase();
        break;

      case TK::ForKeyword:
      case TK::ForeachKeyword:
      case TK::WhileKeyword:
      case TK::RepeatKeyword:
      case TK::ForeverKeyword:
        parseLoop();
        break;

      // All backtick directives (`ifdef, `define, `include, ...) come through
      // the raw Lexer as TokenKind::Directive.  Each occupies its own line.
      case TK::Directive:
        if (isConditionalStartDirective(peek()) &&
            (stop_at_conditional_boundary_ || shouldParseConditionalRegion())) {
          parseConditionalRegion();
        } else {
          parseDirectiveLine();
        }
        break;

      case TK::AssignKeyword:
      case TK::BitKeyword:
      case TK::BreakKeyword:
      case TK::ByteKeyword:
      case TK::GenVarKeyword:
      case TK::IntKeyword:
      case TK::IntegerKeyword:
      case TK::LocalParamKeyword:
      case TK::LogicKeyword:
      case TK::ParameterKeyword:
      case TK::ReturnKeyword:
      case TK::StringKeyword:
      case TK::TimeKeyword:
      case TK::TypedefKeyword:
      case TK::VoidKeyword:
        consumeUntilSemi();
        break;

      default:
        if (slang::parsing::LexerFacts::isKeyword(peek().kind)) {
          parseUnsupportedConstruct();
        } else {
          consumeUntilSemi();
        }
        break;
    }
  }

  // TypeName [#(...)] InstanceName (...);
  auto parseInstantiation() -> void {
    consumeInto(line_);  // type name
    while (at(TK::Directive)) {
      addLine();
      parseDirectiveLine();
    }
    if (at(TK::Hash)) {
      consumeInto(line_);
      consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
      while (at(TK::Directive)) {
        addLine();
        parseDirectiveLine();
      }
    }
    consumeInto(line_);  // instance name
    parsePortListInto(line_);
    if (at(TK::Semicolon)) {
      consumeInto(line_);
    }
    addLine();
  }

  // `ifdef / `define / `include / ... — consume to end of source line
  auto parseDirectiveLine() -> void {
    consumeInto(line_);
    while (pos_ < tokens_.size() && !at(TK::EndOfFile)) {
      if (hasLeadingNewline(peek())) {
        break;
      }
      consumeInto(line_);
    }
    addLine();
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

  // Port list `(port, port, ...)` — each comma-separated port becomes a child
  // UnwrappedLine of the `(` node so the formatter can expand them vertically.
  auto parsePortListInto(Line& line) -> void {
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

        consumeInto(line);
        while (pos_ < tokens_.size() && !at(TK::EndOfFile)) {
          if (hasLeadingNewline(peek())) {
            break;
          }
          consumeInto(line);
        }
        addLine();
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
  auto parseStructuralBlock(TK closeKw) -> void {
    consumeInto(line_);  // module / interface / ...
    // name
    if (!at(closeKw) && !at(TK::Semicolon) && !at(TK::EndOfFile)) {
      consumeInto(line_);
    }
    // optional #(param list) — consumed flat for now
    if (at(TK::Hash)) {
      consumeInto(line_);
      consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
    }
    // port list: each port is a child line of the '(' node
    parsePortListInto(line_);
    if (at(TK::Semicolon)) {
      consumeInto(line_);
    }
    addLine();

    pushOpenFrame(closeKw);
    ++indent_level_;
    parseLevel(closeKw);
    if (at(closeKw)) {
      parseOpenFrameClose();
    }
  }

  // class / function / task ... endclass / endfunction / endtask
  auto parseNamedBlock(TK closeKw) -> void {
    consumeInto(line_);  // keyword
    while (!at(TK::Semicolon) && !at(TK::EndOfFile) && !at(closeKw)) {
      if (at(TK::OpenParenthesis)) {
        consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
      } else {
        consumeInto(line_);
      }
    }
    if (at(TK::Semicolon)) {
      consumeInto(line_);
    }
    addLine();

    pushOpenFrame(closeKw);
    ++indent_level_;
    parseLevel(closeKw);
    if (at(closeKw)) {
      parseOpenFrameClose();
    }
  }

  // generate ... endgenerate
  auto parseSimpleBlock(TK closeKw) -> void {
    consumeInto(line_);
    if (at(TK::Semicolon)) {
      consumeInto(line_);
    }
    addLine();

    pushOpenFrame(closeKw);
    ++indent_level_;
    parseLevel(closeKw);
    if (at(closeKw)) {
      parseOpenFrameClose();
    }
  }

  // begin [:label] ... end [:label]
  auto parseBeginEnd() -> void {
    consumeInto(line_);  // begin
    consumeLabel();
    addLine();

    pushOpenFrame(TK::EndKeyword);
    ++indent_level_;
    parseLevel(TK::EndKeyword);
    if (at(TK::EndKeyword)) {
      parseOpenFrameClose();
    }
  }

  // fork ... join / join_any / join_none
  auto parseFork() -> void {
    consumeInto(line_);  // fork
    consumeLabel();
    addLine();

    ++indent_level_;
    while (pos_ < tokens_.size()) {
      auto k = peek().kind;
      if (k == TK::JoinKeyword || k == TK::JoinAnyKeyword ||
          k == TK::JoinNoneKeyword || k == TK::EndOfFile) {
        break;
      }
      parseStatement();
    }
    --indent_level_;

    consumeInto(line_);  // join / join_any / join_none
    consumeLabel();
    addLine();
  }

  // always / always_comb / always_ff / always_latch / initial / final
  auto parseProceduralBlock() -> void {
    consumeInto(line_);  // keyword
    // optional @(sensitivity list)
    if (at(TK::At)) {
      consumeInto(line_);
      consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
    }
    addLine();

    parseIndentedStatement();
  }

  // if (...) stmt [else [if (...)] stmt]
  auto parseIf() -> void {
    consumeInto(line_);  // if
    consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
    addLine();

    parseIndentedStatement();

    if (at(TK::ElseKeyword)) {
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
  auto parseCase() -> void {
    consumeInto(line_);  // case / casex / casez
    consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
    addLine();

    pushOpenFrame(TK::EndCaseKeyword);
    ++indent_level_;
    while (!at(TK::EndCaseKeyword) && !at(TK::EndOfFile)) {
      if (stop_at_conditional_boundary_ &&
          isConditionalBoundaryDirective(peek())) {
        return;
      }
      if (at(TK::Directive)) {
        if (isConditionalStartDirective(peek()) &&
            (stop_at_conditional_boundary_ || shouldParseConditionalRegion())) {
          parseConditionalRegion();
        } else {
          parseDirectiveLine();
        }
      } else {
        parseCaseItem();
      }
    }

    if (at(TK::EndCaseKeyword)) {
      parseOpenFrameClose();
    }
  }

  auto parseCaseItem() -> void {
    if (at(TK::DefaultKeyword)) {
      consumeInto(line_);
      if (at(TK::Colon)) {
        consumeInto(line_);
      }
    } else {
      while (!at(TK::Colon) && !at(TK::Directive) && !at(TK::EndOfFile) &&
             !at(TK::EndCaseKeyword)) {
        consumeInto(line_);
      }
      if (at(TK::Colon)) {
        consumeInto(line_);
      }
    }
    addLine();

    parseIndentedStatement();
  }

  // for / foreach / while / repeat / forever
  auto parseLoop() -> void {
    consumeInto(line_);  // keyword
    if (at(TK::OpenParenthesis)) {
      consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
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
  SVParser parser(tokens, style.get());
  return parser.parse();
}

}  // namespace format
