#include "pipeline/tree_unwrapper.h"

#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

#include <functional>
#include <gsl/span>
#include <string_view>
#include <utility>
#include <vector>

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

class SVParser {
 public:
  SVParser(gsl::span<const Token> tokens, const FormatStyle& style)
      : tokens_(tokens), style_(style) {}

  auto parse() -> std::vector<Line> {
    parseLevel(TK::EndOfFile);
    return std::move(lines_);
  }

 private:
  gsl::span<const Token> tokens_;
  std::reference_wrapper<const FormatStyle> style_;
  size_t pos_ = 0;
  Line line_;
  std::vector<Line> lines_;
  size_t indent_level_ = 0;

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
      consumeInto(line_);
    }
    if (at(TK::Semicolon)) {
      consumeInto(line_);
    }
    addLine();
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

  // ---- grammar ----

  // NOLINTBEGIN(misc-no-recursion)

  auto parseLevel(TK stopKind) -> void {
    while (pos_ < tokens_.size()) {
      auto kind = peek().kind;
      if (kind == stopKind || kind == TK::EndOfFile) {
        break;
      }
      parseStatement();
    }
  }

  auto parseStatement() -> void {
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
        parseDirectiveLine();
        break;

      default:
        if (at(TK::Identifier) &&
            ((at(TK::Identifier, 1) && at(TK::OpenParenthesis, 2)) ||
             at(TK::Hash, 1))) {
          parseInstantiation();
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

    ++indent_level_;
    parseLevel(closeKw);
    --indent_level_;

    consumeInto(line_);  // endmodule / endinterface / ...
    consumeLabel();
    addLine();
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

    ++indent_level_;
    parseLevel(closeKw);
    --indent_level_;

    consumeInto(line_);  // end keyword
    consumeLabel();
    addLine();
  }

  // generate ... endgenerate
  auto parseSimpleBlock(TK closeKw) -> void {
    consumeInto(line_);
    if (at(TK::Semicolon)) {
      consumeInto(line_);
    }
    addLine();

    ++indent_level_;
    parseLevel(closeKw);
    --indent_level_;

    consumeInto(line_);
    consumeLabel();
    addLine();
  }

  // begin [:label] ... end [:label]
  auto parseBeginEnd() -> void {
    consumeInto(line_);  // begin
    consumeLabel();
    addLine();

    ++indent_level_;
    parseLevel(TK::EndKeyword);
    --indent_level_;

    consumeInto(line_);  // end
    consumeLabel();
    addLine();
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

    ++indent_level_;
    parseStatement();
    --indent_level_;
  }

  // if (...) stmt [else [if (...)] stmt]
  auto parseIf() -> void {
    consumeInto(line_);  // if
    consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
    addLine();

    ++indent_level_;
    parseStatement();
    --indent_level_;

    if (at(TK::ElseKeyword)) {
      consumeInto(line_);  // else
      if (at(TK::IfKeyword)) {
        // else if: `if (...)` is added into the same line_ that already has
        // `else`
        parseIf();
        return;
      }
      addLine();
      ++indent_level_;
      parseStatement();
      --indent_level_;
    }
  }

  // case/casex/casez (...) ... endcase
  auto parseCase() -> void {
    consumeInto(line_);  // case / casex / casez
    consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
    addLine();

    ++indent_level_;
    while (!at(TK::EndCaseKeyword) && !at(TK::EndOfFile)) {
      if (at(TK::Directive)) {
        parseDirectiveLine();
      } else {
        parseCaseItem();
      }
    }
    --indent_level_;

    consumeInto(line_);  // endcase
    addLine();
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

    ++indent_level_;
    parseStatement();
    --indent_level_;
  }

  // for / foreach / while / repeat / forever
  auto parseLoop() -> void {
    consumeInto(line_);  // keyword
    if (at(TK::OpenParenthesis)) {
      consumeBalancedInto(TK::OpenParenthesis, TK::CloseParenthesis, line_);
    }
    addLine();

    ++indent_level_;
    parseStatement();
    --indent_level_;
  }

  // NOLINTEND(misc-no-recursion)
};

}  // namespace

[[nodiscard]] auto TreeUnwrapper::unwrap() const
    -> std::vector<UnwrappedLine<slang::parsing::Token>> {
  SVParser parser(tokens, style.get());
  return parser.parse();
}

}  // namespace format
