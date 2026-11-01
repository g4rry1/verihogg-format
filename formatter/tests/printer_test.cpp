#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "data/format_style.h"
#include "data/lex_context.h"
#include "formatter.h"

namespace {

class PrinterTest : public ::testing::Test {
 protected:
  auto formatText(std::string_view source,
                  format::FormatStyle style = format::FormatStyle::defaults())
      -> std::string {
    tokens_ = ctx_.lex_string(source);
    return format::format(tokens_, style, ctx_.source_text()).formatted_text;
  }

 private:
  LexContext ctx_;
  std::vector<slang::parsing::Token> tokens_;
};

}  // namespace

TEST_F(PrinterTest, PrintsFormattedCode) {
  EXPECT_EQ(formatText("module m (); logic a; endmodule"),
            "module m (\n"
            ");\n"
            "  logic a;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, KeepsWhitespaceAfterEscapedIdentifiers) {
  EXPECT_EQ(formatText("module m; reg \\foo ; assign x = \\foo ; endmodule"),
            "module m;\n"
            "  reg \\foo ;\n"
            "  assign x = \\foo ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, FormatsMacroInvocationAcrossSourceLines) {
  const std::string source =
      "module m(); initial $display(`__LINE__); endmodule\n";
  EXPECT_EQ(formatText(source),
            "module m (\n"
            ");\n"
            "  initial $display (`__LINE__);\n"
            "endmodule\n");
}

TEST_F(PrinterTest, FormatsUnknownMacroCallWithFallbackDiagnostic) {
  const std::string source =
      "module m(); initial $display(`EXTERNAL(1)); endmodule\n";
  LexContext ctx;
  const auto tokens = ctx.lex_string(source);
  const auto result = format::format(tokens, format::FormatStyle::defaults(),
                                     ctx.source_text());
  EXPECT_EQ(result.formatted_text,
            "module m (\n"
            ");\n"
            "  initial $display (`EXTERNAL (1));\n"
            "endmodule\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
}

TEST_F(PrinterTest, FormatsStringifiedMacroInvocation) {
  const std::string source =
      "module m;\n"
      "`define show(expr) $display(`\"expr`\")\n"
      "  initial\n"
      "    begin\n"
      "      `show($bits(x));\n"
      "    end\n"
      "  logic   y ;\n"
      "endmodule\n";
  LexContext ctx;
  const auto tokens = ctx.lex_string(source);
  const auto result = format::format(tokens, format::FormatStyle::defaults(),
                                     ctx.source_text());
  EXPECT_EQ(result.formatted_text,
            "module m;\n"
            "`define show(expr) $display(`\"expr`\")\n"
            "  initial\n"
            "    begin\n"
            "      `show ($bits (x));\n"
            "    end\n"
            "  logic y;\n"
            "endmodule\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
}

TEST_F(PrinterTest, FormatsMacroFromIncludedFile) {
  const std::string source =
      "module m;\n"
      "`include \"defs.svh\"\n"
      "  initial\n"
      "    begin\n"
      "      `SHOW($bits(x));\n"
      "    end\n"
      "  logic   y ;\n"
      "endmodule\n";
  LexContext ctx;
  const auto tokens = ctx.lex_string(source);
  const auto result = format::format(tokens, format::FormatStyle::defaults(),
                                     ctx.source_text());
  EXPECT_EQ(result.formatted_text,
            "module m;\n"
            "`include \"defs.svh\"\n"
            "  initial\n"
            "    begin\n"
            "      `SHOW ($bits (x));\n"
            "    end\n"
            "  logic y;\n"
            "endmodule\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
}

TEST_F(PrinterTest, FormatsNestedMacroCalls) {
  const std::string source =
      "module m;\n"
      "  initial\n"
      "    begin\n"
      "      `OUTER($bits(x), `INNER(a  + b));\n"
      "      `NEXT(c  + d);\n"
      "    end\n"
      "  logic   y ;\n"
      "endmodule\n";
  const auto formatted = formatText(source);
  EXPECT_NE(formatted.find("`OUTER ($bits (x), `INNER (a + b))"),
            std::string::npos);
  EXPECT_NE(formatted.find("`NEXT (c + d)"), std::string::npos);
  EXPECT_NE(formatted.find("  logic y;"), std::string::npos);
}

TEST_F(PrinterTest, PreservesUnsupportedTextAtEndOfFileWithoutNul) {
  EXPECT_EQ(formatText("module m;\nendmodule\n???"),
            "module m;\nendmodule\n???");
}

TEST_F(PrinterTest, PreservesUnsupportedBlockAndFormatsAfterIt) {
  EXPECT_EQ(formatText("module m;\n"
                       "  logic   a ;\n"
                       "  covergroup cg;\n"
                       "    logic should_stay ;\n"
                       "  endgroup\n"
                       "  logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  logic a;\n"
            "  covergroup cg;\n"
            "    logic should_stay ;\n"
            "  endgroup\n"
            "  logic b;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, KeepsBeginAndForkLabelsOnOpeningLine) {
  const std::string source =
      "module m;\n"
      "  always_comb begin : blk\n"
      "    a = b;\n"
      "  end\n"
      "  initial fork : fblk\n"
      "    a = b;\n"
      "  join\n"
      "endmodule\n";
  const std::string expected =
      "module m;\n"
      "  always_comb\n"
      "    begin : blk\n"
      "      a = b;\n"
      "    end\n"
      "  initial\n"
      "    fork : fblk\n"
      "      a = b;\n"
      "    join\n"
      "endmodule\n";
  EXPECT_EQ(formatText(source), expected);
}

TEST_F(PrinterTest, KeepsConditionalDirectivesInInstanceParametersOnOwnLines) {
  const std::string source =
      "module m;\n"
      "  child #(.A(1),\n"
      "`ifdef USE_B\n"
      "    .B(2),\n"
      "`else\n"
      "    .B(3),\n"
      "`endif\n"
      "    .C(4)) inst();\n"
      "endmodule\n";

  const auto formatted = formatText(source);
  EXPECT_NE(formatted.find("\n`ifdef USE_B\n"), std::string::npos);
  EXPECT_NE(formatted.find("\n`else\n"), std::string::npos);
  EXPECT_NE(formatted.find("\n`endif\n"), std::string::npos);
  EXPECT_EQ(formatText(formatted), formatted);
}

TEST_F(PrinterTest, SplitsInstanceParametersWithoutDirectives) {
  const std::string source =
      "module m;\n"
      "  child #(.A(1), .B(2)) inst();\n"
      "endmodule\n";

  const auto formatted = formatText(source);
  EXPECT_NE(formatted.find("child #(\n"), std::string::npos);
  EXPECT_NE(formatted.find("\n  .A (1),\n"), std::string::npos);
  EXPECT_NE(formatted.find("\n  .B (2)\n"), std::string::npos);
  EXPECT_EQ(formatText(formatted), formatted);
}

TEST_F(PrinterTest, RepeatedOpaqueBlocksFormatIdempotently) {
  const std::string source =
      "module m;\n"
      "  covergroup cg1;\n"
      "    x;\n"
      "  endgroup\n"
      "\n"
      "  covergroup cg2;\n"
      "    y;\n"
      "  endgroup\n"
      "  logic   b ;\n"
      "endmodule\n";
  const std::string expected =
      "module m;\n"
      "  covergroup cg1;\n"
      "    x;\n"
      "  endgroup\n"
      "\n"
      "  covergroup cg2;\n"
      "    y;\n"
      "  endgroup\n"
      "  logic b;\n"
      "endmodule\n";
  const auto formatted = formatText(source);
  EXPECT_EQ(formatted, expected);
  EXPECT_EQ(formatText(formatted), formatted);
}

TEST_F(PrinterTest, FormatsAfterUnknownEnclosingBlock) {
  EXPECT_EQ(formatText("module m;\n"
                       "  ??? broken\n"
                       "  logic   raw ;\n"
                       "endmodule\n"
                       "module n;\n"
                       "  logic   formatted ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  ??? broken\n"
            "  logic   raw ;\n"
            "endmodule\n"
            "module n;\n"
            "  logic formatted;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesUnsupportedBlockAndSameLineRemainder) {
  EXPECT_EQ(formatText("module m;\n"
                       "  covergroup cg; endgroup logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  covergroup cg; endgroup logic   b ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesJunkToEndOfModule) {
  EXPECT_EQ(formatText("module m;\n"
                       "  input logic a;\n"
                       "\t???   BAD   8'HFF;  \n"
                       "  logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  input logic a;\n"
            "\t???   BAD   8'HFF;  \n"
            "  logic   b ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesMalformedAssignmentToModuleEnd) {
  EXPECT_EQ(formatText("module m;\n"
                       "  logic   a ;\n"
                       "  assign y  = foo]bar;   // bad\n"
                       "  logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  logic a;\n"
            "  assign y  = foo]bar;   // bad\n"
            "  logic   b ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesMalformedAssignmentAndModuleRemainder) {
  EXPECT_EQ(formatText("module m;\n"
                       "  assign y  = foo]bar; logic   b ;\n"
                       "  logic   c ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  assign y  = foo]bar; logic   b ;\n"
            "  logic   c ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesUnhandledAnnotationTokenAndResumes) {
  EXPECT_EQ(formatText("module m;\n"
                       "  logic   a ;\n"
                       "  assign y  = a inside {1, 2}; // unsupported\n"
                       "  logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  logic a;\n"
            "  assign y  = a inside {1, 2}; // unsupported\n"
            "  logic b;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesMissingTernaryColonToModuleEnd) {
  EXPECT_EQ(formatText("module m;\n"
                       "  assign y  = a ? b;\n"
                       "  logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  assign y  = a ? b;\n"
            "  logic   b ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, TreeRecoveryPreservesMalformedModuleRemainder) {
  EXPECT_EQ(formatText("module m;\n"
                       "  covergroup cg;\n"
                       "  endgroup\n"
                       "  assign y  = foo]bar;\n"
                       "  logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  covergroup cg;\n"
            "  endgroup\n"
            "  assign y  = foo]bar;\n"
            "  logic   b ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesIdentifierLedJunkToEndOfModule) {
  EXPECT_EQ(formatText("module m;\n"
                       "  some_weird_construct nonsense\n"
                       "  logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  some_weird_construct nonsense\n"
            "  logic   b ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesCommentsInsideOpaqueBlock) {
  EXPECT_EQ(formatText("module m;\n"
                       "  logic   a ; // trailing\n"
                       "\n"
                       "  // keep raw comment\n"
                       "  ??? weird   stuff\n"
                       "  logic   b ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  logic a; // trailing\n"
            "\n"
            "  // keep raw comment\n"
            "  ??? weird   stuff\n"
            "  logic   b ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesUnknownTextWithMissingTerminator) {
  EXPECT_EQ(formatText("module m;\n"
                       "  ??? broken\n"
                       "  logic missing\n"
                       "  logic   good ;\n"
                       "endmodule\n"),
            "module m;\n"
            "  ??? broken\n"
            "  logic missing\n"
            "  logic   good ;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesThroughOuterBoundaryWhenNestingIsUnbalanced) {
  EXPECT_EQ(formatText("module m;\n"
                       "  ??? ( broken\n"
                       "  logic should_stay;\n"
                       "endmodule\n"),
            "module m;\n"
            "  ??? ( broken\n"
            "  logic should_stay;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesCrLfThroughEnclosingBlock) {
  format::FormatStyle style = format::FormatStyle::defaults();
  style.line_terminator = format::LineTerminator::kCrLf;
  EXPECT_EQ(formatText("module m;\r\n"
                       "  ???  bad  \r\n"
                       "  logic   b ;\r\n"
                       "endmodule\r\n",
                       style),
            "module m;\r\n"
            "  ???  bad  \r\n"
            "  logic   b ;\r\n"
            "endmodule\r\n");
}

TEST_F(PrinterTest, RespectsCrLfLineTerminator) {
  format::FormatStyle style = format::FormatStyle::defaults();
  style.line_terminator = format::LineTerminator::kCrLf;

  EXPECT_EQ(formatText("module m (); endmodule", style),
            "module m (\r\n"
            ");\r\n"
            "endmodule\r\n");
}

TEST_F(PrinterTest, PreservesLeadingAndTrailingLineComments) {
  EXPECT_EQ(formatText("module m (); // header\n"
                       "// body\n"
                       "logic a; // data\n"
                       "endmodule"),
            "module m (\n"
            "); // header\n"
            "  // body\n"
            "  logic a; // data\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesCommentAfterFinalToken) {
  EXPECT_EQ(formatText("module m;\nendmodule // tail\n"),
            "module m;\nendmodule // tail\n");
  EXPECT_EQ(formatText("module m;\nendmodule\n/* tail */\n"),
            "module m;\nendmodule\n/* tail */\n");
  EXPECT_EQ(formatText("module m; endmodule /* first */ // second"),
            "module m;\nendmodule /* first */ // second");
  EXPECT_EQ(formatText("module m; endmodule\n// tail\n\n"),
            "module m;\nendmodule\n// tail\n\n");
}

TEST_F(PrinterTest, PreservesCommentOnlyFile) {
  EXPECT_EQ(formatText("// only comment\n"), "// only comment\n");
  EXPECT_EQ(formatText("/* only comment */"), "/* only comment */");
}

TEST_F(PrinterTest, PreservesWhitespaceAroundInlineBlockComments) {
  EXPECT_EQ(formatText("module m (); assign y = a/*tight*/+b; "
                       "assign z = a /*left*/+b; assign w = a/*right*/+ b; "
                       "assign v = a /*both*/+ b; endmodule"),
            "module m (\n"
            ");\n"
            "  assign y  = a/*tight*/+ b;\n"
            "  assign z  = a /*left*/+ b;\n"
            "  assign w  = a/*right*/+ b;\n"
            "  assign v  = a /*both*/+ b;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesWhitespaceBeforeTrailingLineComments) {
  EXPECT_EQ(formatText("module m (); logic a;   // spaced\nendmodule"),
            "module m (\n"
            ");\n"
            "  logic a;   // spaced\n"
            "endmodule\n");

  EXPECT_EQ(formatText("module m (); logic a;// tight\nendmodule"),
            "module m (\n"
            ");\n"
            "  logic a;// tight\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesMacroDefinitionsAndFormatsAfterThem) {
  EXPECT_EQ(formatText("`define W 32\n"
                       "// between definitions\n"
                       "\n"
                       "`define WIDTH   `W\n"
                       "`define TAP_ID         'hDEB11001\n"
                       "// after definitions\n"
                       "\n"
                       "module m;\n"
                       "  logic   a ;\n"
                       "endmodule\n"),
            "`define W 32\n"
            "// between definitions\n"
            "\n"
            "`define WIDTH   `W\n"
            "`define TAP_ID         'hDEB11001\n"
            "// after definitions\n"
            "\n"
            "module m;\n"
            "  logic a;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesContinuedMacroDefinition) {
  EXPECT_EQ(formatText("`define SUM(a, b) ((a) + \\\n"
                       "  (b)) // keep spacing\n"
                       "module m;\n"
                       "  logic   a ;\n"
                       "endmodule\n"),
            "`define SUM(a, b) ((a) + \\\n"
            "  (b)) // keep spacing\n"
            "module m;\n"
            "  logic a;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, PreservesMacroDefinitionAtEndOfFile) {
  EXPECT_EQ(formatText("`define WIDTH `W"), "`define WIDTH `W");
}

TEST_F(PrinterTest, PreservesPragmaAndTimescaleDirectiveText) {
  EXPECT_EQ(formatText("`pragma protect end\n"), "`pragma protect end\n");
  EXPECT_EQ(formatText("`timescale 1 ns / 1 ps\n"), "`timescale 1 ns / 1 ps\n");
}

TEST_F(PrinterTest, PrintsCompilerDirectivesAtLeftEdge) {
  EXPECT_EQ(formatText("module m ();\n"
                       "`ifdef FOO\n"
                       "assign y = 8'd0;\n"
                       "`include \"defs.svh\"\n"
                       "`endif\n"
                       "endmodule"),
            "module m (\n"
            ");\n"
            "`ifdef FOO\n"
            "  assign y = 8'd0;\n"
            "`include \"defs.svh\"\n"
            "`endif\n"
            "endmodule\n");
}

TEST_F(PrinterTest, NormalizesNumericLiteralTextBeforeFormatting) {
  EXPECT_EQ(formatText("module m (); assign y = 8'HFF; assign z = 'X; "
                       "assign r = 1E-3; endmodule"),
            "module m (\n"
            ");\n"
            "  assign y  = 8'hff;\n"
            "  assign z  = 'x;\n"
            "  assign r  = 1e-3;\n"
            "endmodule\n");
}

TEST_F(PrinterTest, KeepsSpaceAfterDelayBeforeIdentifier) {
  const auto formatted = formatText(
      "module m; logic s1; initial begin #1 s1 = 1; end endmodule\n");
  EXPECT_NE(formatted.find("#1 s1"), std::string::npos);
}

TEST_F(PrinterTest, KeepsHexDigitsTogetherWhenLexerSplitsAnExponent) {
  const auto formatted = formatText(
      "module m; assign a = 32'h510e527f; "
      "assign b = 32'h2e1b2138; endmodule\n");
  EXPECT_NE(formatted.find("32'h510e527f"), std::string::npos);
  EXPECT_NE(formatted.find("32'h2e1b2138"), std::string::npos);
}

TEST_F(PrinterTest, KeepsBasedLiteralFragmentsAfterBaseWhitespace) {
  const auto formatted = formatText(
      "module m;\n"
      "  initial begin\n"
      "    a = 'h 837FF;\n"
      "    b = 4'b 1x10;\n"
      "    c = 32 'h 12ab_f001;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(formatted.find("'h837FF"), std::string::npos);
  EXPECT_NE(formatted.find("4'b1x10"), std::string::npos);
  EXPECT_NE(formatted.find("32'h12ab_f001"), std::string::npos);
}

TEST_F(PrinterTest, BoundsSearchForNestedTernaryExpressions) {
  constexpr int kNestedTernaryDepth = 16;
  std::string source = "module m; assign out = ";
  for (int i = 0; i < kNestedTernaryDepth; ++i) {
    source += "((sel == 16'b" + std::string(kNestedTernaryDepth - 1 - i, 'x') +
              "1" + std::string(i, '0') + ") ? " + std::to_string(i) + " : ";
  }
  source += "15" + std::string(kNestedTernaryDepth, ')') + "; endmodule\n";

  const auto formatted = formatText(source);
  EXPECT_NE(formatted.find("\n  assign out = "), std::string::npos);
  EXPECT_EQ(std::count(formatted.begin(), formatted.end(), '?'),
            kNestedTernaryDepth);
  EXPECT_NE(formatted.find("endmodule"), std::string::npos);
}

TEST_F(PrinterTest, DoesNotInsertBeginEndDuringNormalization) {
  EXPECT_EQ(formatText("module m (); always_ff @(posedge clk) if (en) q <= d; "
                       "endmodule"),
            "module m (\n"
            ");\n"
            "  always_ff @(posedge clk)\n"
            "    if (en) q <= d;\n"
            "endmodule\n");
}
