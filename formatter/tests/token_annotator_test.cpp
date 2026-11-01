#include "pipeline/token_annotator.h"

#include <gtest/gtest.h>
#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

#include <string>
#include <string_view>
#include <vector>

#include "data/format_style.h"
#include "data/format_token.h"
#include "data/lex_context.h"
#include "pipeline/tree_unwrapper.h"

namespace {

using FT = format::FormatToken;

class TokenAnnotatorTest : public ::testing::Test {
 protected:
  auto annotateWithDiagnostics(std::string_view source)
      -> format::AnnotationResult {
    auto tokens = ctx_.lex_string(source);
    auto unwrapped =
        format::TreeUnwrapper(tokens, style, ctx_.source_text()).unwrap();
    return format::TokenAnnotator(style).annotateWithDiagnostics(
        unwrapped, ctx_.source_text());
  }

  auto annotateTokens(std::string_view source)
      -> std::vector<format::UnwrappedLine<FT>> {
    auto tokens = ctx_.lex_string(source);
    auto unwrapped = format::TreeUnwrapper(tokens, style).unwrap();
    return format::TokenAnnotator(style).annotate(unwrapped,
                                                  ctx_.source_text());
  }

 private:
  format::FormatStyle style = format::FormatStyle::defaults();
  LexContext ctx_;
};

TEST_F(TokenAnnotatorTest, ParserPreservesMalformedBracketBeforeAnnotation) {
  auto result = annotateWithDiagnostics(
      "module m;\n"
      "  logic a;\n"
      "  assign y  = foo]bar;   // bad\n"
      "  logic b;\n"
      "endmodule\n");
  EXPECT_TRUE(result.warnings.empty());
  size_t opaque_count = 0;
  for (const auto& line : result.lines) {
    if (line.is_opaque) {
      ++opaque_count;
      EXPECT_NE(line.raw_text.find("assign y  = foo]bar;"), std::string::npos);
      EXPECT_NE(line.raw_text.find("logic b;"), std::string::npos);
    }
  }
  EXPECT_EQ(opaque_count, 1U);
}

TEST_F(TokenAnnotatorTest, BasedLiteralWildcardsStayExact) {
  auto result = annotateWithDiagnostics(
      "module m;\n"
      "  initial begin\n"
      "    casez (x)\n"
      "      4'b10??: y = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "invalid-annotation");
  size_t opaque_count = 0;
  for (const auto& line : result.lines) {
    if (line.is_opaque) {
      ++opaque_count;
      EXPECT_EQ(line.raw_text, "\n      4'b10??: y = 1;\n");
    }
  }
  EXPECT_EQ(opaque_count, 1U);
}

TEST_F(TokenAnnotatorTest, BalancedExpressionRemainsFormattable) {
  auto result = annotateWithDiagnostics(
      "module m (input logic a);\n"
      "  assign y = (a ? 1 : 0);\n"
      "  assign z = 'x;\n"
      "endmodule\n");
  EXPECT_TRUE(result.warnings.empty());
  for (const auto& line : result.lines) {
    EXPECT_FALSE(line.is_opaque);
  }
}

TEST_F(TokenAnnotatorTest, UnhandledTokenBecomesOpaqueWithWarning) {
  auto result = annotateWithDiagnostics(
      "module m;\n"
      "  assign y  = a inside {1, 2}; // unsupported\n"
      "  logic   b ;\n"
      "endmodule\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "invalid-annotation");
  EXPECT_NE(result.warnings.front().message.find("unsupported token kind"),
            std::string::npos);
  ASSERT_EQ(result.lines.size(), 5U);
  EXPECT_TRUE(result.lines.at(1).is_opaque);
  EXPECT_EQ(result.lines.at(1).raw_text,
            "\n  assign y  = a inside {1, 2}; // unsupported\n");
  EXPECT_FALSE(result.lines.at(2).is_opaque);
  for (const auto& token : result.lines.at(2).tokens) {
    EXPECT_NE(token.type, format::TokenType::kUnknown);
  }
  EXPECT_EQ(result.lines.back().tokens.front().token.kind,
            slang::parsing::TokenKind::EndOfFile);
}

TEST_F(TokenAnnotatorTest, RecognizedGenericTokensAreNotUnknown) {
  auto result = annotateWithDiagnostics(
      "module m;\n"
      "  localparam int N = 4;\n"
      "  logic [N-1:0] a;\n"
      "  assign y = (a ? '1 : '0);\n"
      "endmodule\n");
  EXPECT_TRUE(result.warnings.empty());
  for (const auto& line : result.lines) {
    EXPECT_FALSE(line.is_opaque);
    for (const auto& token : line.tokens) {
      EXPECT_NE(token.type, format::TokenType::kUnknown);
    }
  }
}

TEST_F(TokenAnnotatorTest, DirectiveArgumentMustNotBreak) {
  auto lines = annotateTokens("`include \"file.svh\"");
  ASSERT_FALSE(lines.empty());
  const auto& line = lines.at(0);
  ASSERT_GE(line.tokens.size(), 2);

  const FT* argument = nullptr;
  for (size_t i = 0; i + 1 < line.tokens.size(); ++i) {
    if (line.tokens.at(i).type == format::TokenType::kDirective) {
      argument = &line.tokens.at(i + 1);
      break;
    }
  }
  ASSERT_NE(argument, nullptr) << "No token after directive";

  EXPECT_EQ(argument->before.break_decision,
            format::BreakDecision::kMustNotBreak)
      << "Argument after directive must stay on same line";
}

TEST_F(TokenAnnotatorTest, DirectiveArgumentMustStayWithMatchingParen) {
  auto lines = annotateTokens("`if (EXPR)");
  ASSERT_FALSE(lines.empty());
  const auto& line = lines.at(0);
  ASSERT_GE(line.tokens.size(), 2);

  const FT* argument = nullptr;
  for (size_t i = 0; i + 1 < line.tokens.size(); ++i) {
    if (line.tokens.at(i).type == format::TokenType::kDirective) {
      argument = &line.tokens.at(i + 1);
      break;
    }
  }
  ASSERT_NE(argument, nullptr) << "No token after directive";
  EXPECT_EQ(argument->before.break_decision,
            format::BreakDecision::kMustNotBreak)
      << "Token after directive keyword must not break";
}

}  // namespace
