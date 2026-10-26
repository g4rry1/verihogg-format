#include <gtest/gtest.h>
#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

#include <algorithm>
#include <cstddef>
#include <ostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "data/format_style.h"
#include "data/lex_context.h"
#include "data/unwrapped_line.h"
#include "pipeline/tree_unwrapper.h"

namespace {

using TK = slang::parsing::TokenKind;
using Line = format::UnwrappedLine<slang::parsing::Token>;
using PP = format::PartitionPolicy;

constexpr size_t kColumnLimit = 100;
constexpr size_t kIndent = 2;

// ---------------------------------------------------------------------------
// Snapshot types — a lightweight copy of the tree that supports operator==
// and can be built by hand for expected values.
// ---------------------------------------------------------------------------

struct TokSnap {
  TK kind;
  std::string text;
  auto operator==(const TokSnap&) const -> bool = default;
};

struct LineSnap {
  std::vector<TokSnap> tokens;
  size_t indent = 0;
  auto operator==(const LineSnap& other) const -> bool = default;
};

// Converters from real lines to snapshots.

auto snap(const slang::parsing::Token& t) -> TokSnap {
  return {.kind = t.kind, .text = std::string(t.rawText())};
}

auto snap(const Line& l) -> LineSnap {
  LineSnap s{.indent = l.indentation_spaces};
  for (const auto& token : l.tokens) {
    s.tokens.push_back(snap(token));
  }
  return s;
}

auto snap(const std::vector<Line>& lines) -> std::vector<LineSnap> {
  std::vector<LineSnap> result;
  result.reserve(lines.size());
  for (const auto& l : lines) {
    // These snapshots describe source constructs; EOF is tested separately.
    if (l.tokens.size() == 1 && l.tokens.front().kind == TK::EndOfFile) {
      continue;
    }
    result.push_back(snap(l));
  }
  return result;
}

// Builders for constructing expected snapshots by hand.

// N — build a token snapshot from its kind and raw text.
auto N(TK kind, std::string_view text) -> TokSnap {
  return {.kind = kind, .text = std::string(text)};
}

// L — build a line snapshot from indent level, partition policy, and tokens.
auto L(size_t indent, PP policy, std::vector<TokSnap> tokens) -> LineSnap {
  return {.tokens = std::move(tokens), .indent = indent};
}

auto policyName(PP policy) -> std::string_view {
  switch (policy) {
    case PP::kAlwaysExpand:
      return "AlwaysExpand";
    case PP::kFitOnLineElseExpand:
      return "FitOnLineElseExpand";
    case PP::kAssignmentAlignment:
      return "AssignmentAlignment";
    case PP::kTabularAlignment:
      return "TabularAlignment";
    case PP::kAlreadyFormatted:
      return "AlreadyFormatted";
  }
  return "Unknown";
}

auto operator<<(std::ostream& os, const TokSnap& tok) -> std::ostream& {
  return os << slang::parsing::toString(tok.kind) << "(" << tok.text << ")";
}

auto operator<<(std::ostream& os, const LineSnap& line) -> std::ostream& {
  os << "{indent=" << line.indent << ", tokens=";
  ::testing::internal::UniversalPrint(line.tokens, &os);
  return os << "}";
}

// ---------------------------------------------------------------------------
// Fixture — keeps LexContext alive so token memory outlives UnwrappedLine.
// GTest creates a fresh instance per TEST_F, so no shared state between tests.
// ---------------------------------------------------------------------------

class TreeUnwrapperTest : public ::testing::Test {
 protected:
  auto expectTokenConservation(const std::vector<Line>& lines) const -> void {
    size_t index = 0;
    for (const auto& line : lines) {
      for (const auto& token : line.tokens) {
        ASSERT_LT(index, tokens_.size());
        EXPECT_EQ(token.kind, tokens_[index].kind);
        EXPECT_EQ(token.rawText(), tokens_[index].rawText());
        EXPECT_EQ(token.location(), tokens_[index].location());
        ++index;
      }
    }
    EXPECT_EQ(index, tokens_.size());
  }

  auto parse(std::string_view src) -> std::vector<Line> {
    tokens_ = ctx_.lex_string(src);
    const format::FormatStyle style = {.column_limit = kColumnLimit,
                                       .indentation_spaces = kIndent};
    auto lines =
        format::TreeUnwrapper(tokens_, style, ctx_.source_text()).unwrap();
    expectTokenConservation(lines);
    return lines;
  }

  auto parseWithDiagnostics(std::string_view src) -> format::UnwrapResult {
    tokens_ = ctx_.lex_string(src);
    const format::FormatStyle style = {.column_limit = kColumnLimit,
                                       .indentation_spaces = kIndent};
    auto result = format::TreeUnwrapper(tokens_, style, ctx_.source_text())
                      .unwrapWithDiagnostics();
    expectTokenConservation(result.lines);
    return result;
  }

 private:
  LexContext ctx_;
  std::vector<slang::parsing::Token> tokens_;
};

}  // namespace

// NOLINTBEGIN(misc-use-internal-linkage,bugprone-throwing-static-initialization,cert-err58-cpp,cppcoreguidelines-owning-memory,modernize-use-trailing-return-type)

// ---- module header ----------------------------------------------------------

TEST_F(TreeUnwrapperTest, ModuleHeaderWithoutPorts) {
  auto lines = parse("module foo (); endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "foo"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, ThreePortsBecomeThreeLines) {
  auto lines = parse(
      "module counter (input logic clk, input logic rst_n, output logic [3:0] "
      "count);"
      " endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "counter"),
            N(TK::OpenParenthesis, "("),
        }),
      // port 0: input logic clk ,
      L(0, PP::kTabularAlignment,
        {
            N(TK::InputKeyword, "input"),
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "clk"),
            N(TK::Comma, ","),
        }),
      // port 1: input logic rst_n ,
      L(0, PP::kTabularAlignment,
        {
            N(TK::InputKeyword, "input"),
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "rst_n"),
            N(TK::Comma, ","),
        }),
      // port 2: output logic [3:0] count  — no trailing comma
      L(0, PP::kTabularAlignment,
        {
            N(TK::OutputKeyword, "output"),
            N(TK::LogicKeyword, "logic"),
            N(TK::OpenBracket, "["),
            N(TK::IntegerLiteral, "3"),
            N(TK::Colon, ":"),
            N(TK::IntegerLiteral, "0"),
            N(TK::CloseBracket, "]"),
            N(TK::Identifier, "count"),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, BodyDeclarationsWithKeywordsUseTabularAlignment) {
  auto lines = parse("module m (); logic a; output logic y; endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent, PP::kTabularAlignment,
        {
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "a"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent, PP::kTabularAlignment,
        {
            N(TK::OutputKeyword, "output"),
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "y"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, ParameterizedInstantiationIsParsedBeforeFallback) {
  auto lines = parse("module m (); child #(8) u_child (clk, rst_n); endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent, PP::kFitOnLineElseExpand,
        {
            N(TK::Identifier, "child"),
            N(TK::Hash, "#"),
            N(TK::OpenParenthesis, "("),
        }),
      L(kIndent, PP::kFitOnLineElseExpand,
        {
            N(TK::IntegerLiteral, "8"),
        }),
      L(kIndent, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Identifier, "u_child"),
            N(TK::OpenParenthesis, "("),
        }),
      L(kIndent, PP::kTabularAlignment,
        {
            N(TK::Identifier, "clk"),
            N(TK::Comma, ","),
        }),
      L(kIndent, PP::kTabularAlignment,
        {
            N(TK::Identifier, "rst_n"),
        }),
      L(kIndent, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, MultipleInstancesCompleteOneAnnexAItem) {
  const auto result =
      parseWithDiagnostics("module m; child u0(a), u1(b); endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_first = false;
  bool found_second = false;
  for (const auto& line : result.lines) {
    for (const auto& token : line.tokens) {
      found_first |= token.rawText() == "u0";
      found_second |= token.rawText() == "u1";
    }
  }
  EXPECT_TRUE(found_first);
  EXPECT_TRUE(found_second);
}

TEST_F(TreeUnwrapperTest, MprfConditionalPortsKeepDirectivesAsLines) {
  auto lines = parse(
      "`include \"scr1_arch_description.svh\"\n"
      "module scr1_pipe_mprf (\n"
      "`ifdef SCR1_MPRF_RST_EN\n"
      "input logic rst_n,\n"
      "`endif\n"
      "input logic clk\n"
      ");"
      "endmodule : scr1_pipe_mprf");

  const std::vector<LineSnap> expected = {
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`include"),
            N(TK::StringLiteral, "\"scr1_arch_description.svh\""),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "scr1_pipe_mprf"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`ifdef"),
            N(TK::Identifier, "SCR1_MPRF_RST_EN"),
        }),
      L(0, PP::kTabularAlignment,
        {
            N(TK::InputKeyword, "input"),
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "rst_n"),
            N(TK::Comma, ","),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`endif"),
        }),
      L(0, PP::kTabularAlignment,
        {
            N(TK::InputKeyword, "input"),
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "clk"),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
            N(TK::Colon, ":"),
            N(TK::Identifier, "scr1_pipe_mprf"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, PortListKeepsUnknownBacktickAsMacroUsage) {
  auto lines = parse(
      "module m (`SCR1_PORT(input logic a, b), input logic c); endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kTabularAlignment,
        {
            N(TK::Directive, "`SCR1_PORT"),
            N(TK::OpenParenthesis, "("),
            N(TK::InputKeyword, "input"),
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "a"),
            N(TK::Comma, ","),
            N(TK::Identifier, "b"),
            N(TK::CloseParenthesis, ")"),
            N(TK::Comma, ","),
        }),
      L(0, PP::kTabularAlignment,
        {
            N(TK::InputKeyword, "input"),
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "c"),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, MprfRamAttributeDeclarationsStayFlat) {
  auto lines = parse(
      "module m ();\n"
      "`ifdef SCR1_TRGT_FPGA_INTEL_MAX10\n"
      "(* ramstyle = \"M9K\" *) logic [`SCR1_XLEN-1:0] mprf_int "
      "[1:`SCR1_MPRF_SIZE-1];\n"
      "`else\n"
      "type_scr1_mprf_v [1:`SCR1_MPRF_SIZE-1] mprf_int;\n"
      "`endif\n"
      "endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`ifdef"),
            N(TK::Identifier, "SCR1_TRGT_FPGA_INTEL_MAX10"),
        }),
      L(kIndent, PP::kTabularAlignment,
        {
            N(TK::OpenParenthesis, "("),
            N(TK::Star, "*"),
            N(TK::Identifier, "ramstyle"),
            N(TK::Equals, "="),
            N(TK::StringLiteral, "\"M9K\""),
            N(TK::Star, "*"),
            N(TK::CloseParenthesis, ")"),
            N(TK::LogicKeyword, "logic"),
            N(TK::OpenBracket, "["),
            N(TK::Directive, "`SCR1_XLEN"),
            N(TK::Minus, "-"),
            N(TK::IntegerLiteral, "1"),
            N(TK::Colon, ":"),
            N(TK::IntegerLiteral, "0"),
            N(TK::CloseBracket, "]"),
            N(TK::Identifier, "mprf_int"),
            N(TK::OpenBracket, "["),
            N(TK::IntegerLiteral, "1"),
            N(TK::Colon, ":"),
            N(TK::Directive, "`SCR1_MPRF_SIZE"),
            N(TK::Minus, "-"),
            N(TK::IntegerLiteral, "1"),
            N(TK::CloseBracket, "]"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`else"),
        }),
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::Identifier, "type_scr1_mprf_v"),
            N(TK::OpenBracket, "["),
            N(TK::IntegerLiteral, "1"),
            N(TK::Colon, ":"),
            N(TK::Directive, "`SCR1_MPRF_SIZE"),
            N(TK::Minus, "-"),
            N(TK::IntegerLiteral, "1"),
            N(TK::CloseBracket, "]"),
            N(TK::Identifier, "mprf_int"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`endif"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, ConditionalModuleBranchesShareEndmodule) {
  auto result = parseWithDiagnostics(
      "`ifdef USE_A\n"
      "module m_a ();\n"
      "`else\n"
      "module m_b ();\n"
      "`endif\n"
      "logic x;\n"
      "endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`ifdef"),
            N(TK::Identifier, "USE_A"),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m_a"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`else"),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m_b"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`endif"),
        }),
      L(kIndent, PP::kTabularAlignment,
        {
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "x"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(snap(result.lines), expected);
}

TEST_F(TreeUnwrapperTest,
       ConditionalModuleBranchesCanHavePreludeBeforeSharedEndmodule) {
  auto result = parseWithDiagnostics(
      "`ifdef USE_A\n"
      "localparam int SELECTED = 0;\n"
      "module m_a ();\n"
      "`else\n"
      "localparam int SELECTED = 1;\n"
      "module m_b ();\n"
      "`endif\n"
      "logic x;\n"
      "endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`ifdef"),
            N(TK::Identifier, "USE_A"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::LocalParamKeyword, "localparam"),
            N(TK::IntKeyword, "int"),
            N(TK::Identifier, "SELECTED"),
            N(TK::Equals, "="),
            N(TK::IntegerLiteral, "0"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m_a"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`else"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::LocalParamKeyword, "localparam"),
            N(TK::IntKeyword, "int"),
            N(TK::Identifier, "SELECTED"),
            N(TK::Equals, "="),
            N(TK::IntegerLiteral, "1"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m_b"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`endif"),
        }),
      L(kIndent, PP::kTabularAlignment,
        {
            N(TK::LogicKeyword, "logic"),
            N(TK::Identifier, "x"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(snap(result.lines), expected);
}

// ---- always_ff --------------------------------------------------------------

TEST_F(TreeUnwrapperTest, AlwaysFFIsOwnLine) {
  auto lines =
      parse("module m (); always_ff @(posedge clk) begin end endmodule");

  const std::vector<LineSnap> expected = {
      // module m ();
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      // always_ff @(posedge clk)  — indent 1*kIndent
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::AlwaysFFKeyword, "always_ff"),
            N(TK::At, "@"),
            N(TK::OpenParenthesis, "("),
            N(TK::PosEdgeKeyword, "posedge"),
            N(TK::Identifier, "clk"),
            N(TK::CloseParenthesis, ")"),
        }),
      // begin  — indent 2*kIndent
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      // end  — indent 2*kIndent
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      // endmodule
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, ConditionalAlwaysFFBranchesShareBeginEndBody) {
  auto result = parseWithDiagnostics(
      "module m ();\n"
      "`ifndef USE_ALT_CLK\n"
      "always_ff @(posedge clk) begin\n"
      "`else\n"
      "always_ff @(posedge alt_clk) begin\n"
      "`endif\n"
      "if (rst) begin\n"
      "q <= d;\n"
      "end\n"
      "end\n"
      "endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`ifndef"),
            N(TK::Identifier, "USE_ALT_CLK"),
        }),
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::AlwaysFFKeyword, "always_ff"),
            N(TK::At, "@"),
            N(TK::OpenParenthesis, "("),
            N(TK::PosEdgeKeyword, "posedge"),
            N(TK::Identifier, "clk"),
            N(TK::CloseParenthesis, ")"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`else"),
        }),
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::AlwaysFFKeyword, "always_ff"),
            N(TK::At, "@"),
            N(TK::OpenParenthesis, "("),
            N(TK::PosEdgeKeyword, "posedge"),
            N(TK::Identifier, "alt_clk"),
            N(TK::CloseParenthesis, ")"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`endif"),
        }),
      L(kIndent * 3, PP::kAlwaysExpand,
        {
            N(TK::IfKeyword, "if"),
            N(TK::OpenParenthesis, "("),
            N(TK::Identifier, "rst"),
            N(TK::CloseParenthesis, ")"),
        }),
      L(kIndent * 4, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      L(kIndent * 5, PP::kAlwaysExpand,
        {
            N(TK::Identifier, "q"),
            N(TK::LessThanEquals, "<="),
            N(TK::Identifier, "d"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent * 4, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(snap(result.lines), expected);
}

TEST_F(TreeUnwrapperTest, MprfResetAlwaysFFWithAggregateLiteral) {
  auto lines = parse(
      "module m ();\n"
      "`ifdef SCR1_MPRF_RST_EN\n"
      "always_ff @(posedge clk, negedge rst_n) begin "
      "if (~rst_n) begin "
      "mprf_int <= '{default: '0}; "
      "end else if (wr_req_vd) begin "
      "mprf_int[exu2mprf_rd_addr_i] <= exu2mprf_rd_data_i; "
      "end "
      "end\n"
      "`endif\n"
      "endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`ifdef"),
            N(TK::Identifier, "SCR1_MPRF_RST_EN"),
        }),
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::AlwaysFFKeyword, "always_ff"),
            N(TK::At, "@"),
            N(TK::OpenParenthesis, "("),
            N(TK::PosEdgeKeyword, "posedge"),
            N(TK::Identifier, "clk"),
            N(TK::Comma, ","),
            N(TK::NegEdgeKeyword, "negedge"),
            N(TK::Identifier, "rst_n"),
            N(TK::CloseParenthesis, ")"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      L(kIndent * 3, PP::kAlwaysExpand,
        {
            N(TK::IfKeyword, "if"),
            N(TK::OpenParenthesis, "("),
            N(TK::Tilde, "~"),
            N(TK::Identifier, "rst_n"),
            N(TK::CloseParenthesis, ")"),
        }),
      L(kIndent * 4, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      L(kIndent * 5, PP::kAlwaysExpand,
        {
            N(TK::Identifier, "mprf_int"),
            N(TK::LessThanEquals, "<="),
            N(TK::ApostropheOpenBrace, "'{"),
            N(TK::DefaultKeyword, "default"),
            N(TK::Colon, ":"),
            N(TK::UnbasedUnsizedLiteral, "'0"),
            N(TK::CloseBrace, "}"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent * 4, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      L(kIndent * 3, PP::kAlwaysExpand,
        {
            N(TK::ElseKeyword, "else"),
            N(TK::IfKeyword, "if"),
            N(TK::OpenParenthesis, "("),
            N(TK::Identifier, "wr_req_vd"),
            N(TK::CloseParenthesis, ")"),
        }),
      L(kIndent * 4, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      L(kIndent * 5, PP::kAlwaysExpand,
        {
            N(TK::Identifier, "mprf_int"),
            N(TK::OpenBracket, "["),
            N(TK::Identifier, "exu2mprf_rd_addr_i"),
            N(TK::CloseBracket, "]"),
            N(TK::LessThanEquals, "<="),
            N(TK::Identifier, "exu2mprf_rd_data_i"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent * 4, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`endif"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, MprfSimulationAssertionStaysSingleStatementLine) {
  auto lines = parse(
      "module m ();\n"
      "`ifdef SCR1_TRGT_SIMULATION\n"
      "SCR1_SVA_MPRF_WRITEX : assert property ("
      "@(negedge clk) disable iff (~rst_n) "
      "exu2mprf_w_req_i |-> !$isunknown({exu2mprf_rd_addr_i, "
      "(|exu2mprf_rd_addr_i ? exu2mprf_rd_data_i : `SCR1_XLEN'd0)})"
      ") else $error(\"MPRF error: unknown values\");\n"
      "`endif\n"
      "endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`ifdef"),
            N(TK::Identifier, "SCR1_TRGT_SIMULATION"),
        }),
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::Identifier, "SCR1_SVA_MPRF_WRITEX"),
            N(TK::Colon, ":"),
            N(TK::AssertKeyword, "assert"),
            N(TK::PropertyKeyword, "property"),
            N(TK::OpenParenthesis, "("),
            N(TK::At, "@"),
            N(TK::OpenParenthesis, "("),
            N(TK::NegEdgeKeyword, "negedge"),
            N(TK::Identifier, "clk"),
            N(TK::CloseParenthesis, ")"),
            N(TK::DisableKeyword, "disable"),
            N(TK::IffKeyword, "iff"),
            N(TK::OpenParenthesis, "("),
            N(TK::Tilde, "~"),
            N(TK::Identifier, "rst_n"),
            N(TK::CloseParenthesis, ")"),
            N(TK::Identifier, "exu2mprf_w_req_i"),
            N(TK::OrMinusArrow, "|->"),
            N(TK::Exclamation, "!"),
            N(TK::SystemIdentifier, "$isunknown"),
            N(TK::OpenParenthesis, "("),
            N(TK::OpenBrace, "{"),
            N(TK::Identifier, "exu2mprf_rd_addr_i"),
            N(TK::Comma, ","),
            N(TK::OpenParenthesis, "("),
            N(TK::Or, "|"),
            N(TK::Identifier, "exu2mprf_rd_addr_i"),
            N(TK::Question, "?"),
            N(TK::Identifier, "exu2mprf_rd_data_i"),
            N(TK::Colon, ":"),
            N(TK::Directive, "`SCR1_XLEN"),
            N(TK::IntegerBase, "'d"),
            N(TK::IntegerLiteral, "0"),
            N(TK::CloseParenthesis, ")"),
            N(TK::CloseBrace, "}"),
            N(TK::CloseParenthesis, ")"),
            N(TK::CloseParenthesis, ")"),
            N(TK::ElseKeyword, "else"),
            N(TK::SystemIdentifier, "$error"),
            N(TK::OpenParenthesis, "("),
            N(TK::StringLiteral, "\"MPRF error: unknown values\""),
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`endif"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, LabeledAssertionElseBeginParsesActionBlock) {
  auto result = parseWithDiagnostics(
      "module m ();\n"
      "`ifdef SIM\n"
      "A_CHECK : assert property (@(posedge clk) ok) else begin\n"
      "$error(\"bad\");\n"
      "end\n"
      "`endif\n"
      "endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`ifdef"),
            N(TK::Identifier, "SIM"),
        }),
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::Identifier, "A_CHECK"),
            N(TK::Colon, ":"),
            N(TK::AssertKeyword, "assert"),
            N(TK::PropertyKeyword, "property"),
            N(TK::OpenParenthesis, "("),
            N(TK::At, "@"),
            N(TK::OpenParenthesis, "("),
            N(TK::PosEdgeKeyword, "posedge"),
            N(TK::Identifier, "clk"),
            N(TK::CloseParenthesis, ")"),
            N(TK::Identifier, "ok"),
            N(TK::CloseParenthesis, ")"),
            N(TK::ElseKeyword, "else"),
            N(TK::BeginKeyword, "begin"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::SystemIdentifier, "$error"),
            N(TK::OpenParenthesis, "("),
            N(TK::StringLiteral, "\"bad\""),
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::Directive, "`endif"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(snap(result.lines), expected);
}

// ---- begin/end --------------------------------------------------------------

TEST_F(TreeUnwrapperTest, BeginEndAreOwnLines) {
  auto lines = parse("module m (); always_comb begin end endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      // always_comb has no sensitivity list, so no @ token
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::AlwaysCombKeyword, "always_comb"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

// ---- if ---------------------------------------------------------------------

TEST_F(TreeUnwrapperTest, IfIsOwnLine) {
  auto lines =
      parse("module m (); always_comb begin if (a) b = 1; end endmodule");

  const std::vector<LineSnap> expected = {
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::ModuleKeyword, "module"),
            N(TK::Identifier, "m"),
            N(TK::OpenParenthesis, "("),
        }),
      L(0, PP::kFitOnLineElseExpand,
        {
            N(TK::CloseParenthesis, ")"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent, PP::kAlwaysExpand,
        {
            N(TK::AlwaysCombKeyword, "always_comb"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::BeginKeyword, "begin"),
        }),
      // if (a)  — indent 3*kIndent (inside begin, inside always_comb, inside
      // module)
      L(kIndent * 3, PP::kAlwaysExpand,
        {
            N(TK::IfKeyword, "if"),
            N(TK::OpenParenthesis, "("),
            N(TK::Identifier, "a"),
            N(TK::CloseParenthesis, ")"),
        }),
      // b = 1;  — indent 4*kIndent
      L(kIndent * 4, PP::kAlwaysExpand,
        {
            N(TK::Identifier, "b"),
            N(TK::Equals, "="),
            N(TK::IntegerLiteral, "1"),
            N(TK::Semicolon, ";"),
        }),
      L(kIndent * 2, PP::kAlwaysExpand,
        {
            N(TK::EndKeyword, "end"),
        }),
      L(0, PP::kAlwaysExpand,
        {
            N(TK::EndModuleKeyword, "endmodule"),
        }),
  };

  EXPECT_EQ(snap(lines), expected);
}

TEST_F(TreeUnwrapperTest, MacroCastDoesNotTriggerIdentifierRecovery) {
  auto result = parseWithDiagnostics(
      "module m;\n"
      "  always_comb begin\n"
      "    data = `WIDTH'(other);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  EXPECT_NE(result.warnings.front().message.find("macro expansion"),
            std::string::npos);
  for (const auto& line : result.lines) {
    EXPECT_FALSE(line.is_opaque);
  }
}

TEST_F(TreeUnwrapperTest, IdentifierStatementsContinueAcrossSourceLines) {
  auto result = parseWithDiagnostics(
      "module m;\n"
      "  initial begin\n"
      "    value = a &\n"
      "            b +\n"
      "            int'(c);\n"
      "    next = value +\n"
      "           d;\n"
      "    casted =\n"
      "             int'(next);\n"
      "    incremented = ++\n"
      "                  next;\n"
      "  end\n"
      "endmodule\n");

  EXPECT_TRUE(result.warnings.empty());
  size_t assignment_count = 0;
  for (const auto& line : result.lines) {
    EXPECT_FALSE(line.is_opaque);
    if (line.tokens.empty()) {
      continue;
    }
    const auto first = line.tokens.front().rawText();
    if (first == "value" || first == "next" || first == "casted" ||
        first == "incremented") {
      ++assignment_count;
      EXPECT_EQ(line.tokens.back().kind, TK::Semicolon);
      bool saw_continuation = false;
      for (const auto& token : line.tokens) {
        if (token.rawText() == (first == "value"  ? "c"
                                : first == "next" ? "d"
                                                  : "next")) {
          saw_continuation = true;
        }
      }
      EXPECT_TRUE(saw_continuation);
    }
  }
  EXPECT_EQ(assignment_count, 4U);
}

TEST_F(TreeUnwrapperTest, IdentifierRecoveryKeepsUnknownStatement) {
  auto result = parseWithDiagnostics(
      "module m;\n"
      "  mystery words\n"
      "  next = 1;\n"
      "endmodule\n");

  ASSERT_EQ(result.warnings.size(), 1U);
  bool preserved_following_statement = false;
  for (const auto& line : result.lines) {
    if (line.is_opaque &&
        line.raw_text.find("  next = 1;") != std::string::npos) {
      preserved_following_statement = true;
    }
  }
  EXPECT_TRUE(preserved_following_statement);
}

TEST_F(TreeUnwrapperTest, AnnexAParsesFormerlyOpaqueConstructs) {
  for (const std::string_view source : {
           "module m; covergroup cg; cp: coverpoint a; endgroup endmodule",
           "module m; property p; a |-> b; endproperty endmodule",
           "module m; sequence s; a ##1 b; endsequence endmodule",
           "module m; clocking cb @(posedge clk); input a; endclocking "
           "endmodule",
           "checker c(input logic a); assert property (a); endchecker",
           "module m; specify specparam t = 1; endspecify endmodule",
           "config cfg; design lib.top; default liblist lib; endconfig",
           "primitive p(out, a); output out; input a; table 0 : 0; 1 : 1; "
           "endtable endprimitive",
           "class c; rand int x; constraint r { x inside {[0:3]}; } endclass",
           "class c; static constraint r { x > 0; } endclass",
           "module m; covergroup cg @(posedge clk); cp: coverpoint a { bins "
           "zero = {0}; } endgroup endmodule",
           "module m; default clocking cb @(posedge clk); input a; endclocking "
           "endmodule",
           "module m; global clocking cb @(posedge clk); endclocking endmodule",
           "module m; specify (a => b) = 1; endspecify endmodule",
           "config cfg; localparam int W = 1; design lib.top; instance top.u "
           "use lib.foo; endconfig",
           "primitive p(output out, input a); table 0 : 0; 1 : 1; endtable "
           "endprimitive",
           "primitive p(out, a); output reg out; input a; initial out = 1'b0; "
           "table 0 : 0 : 0; 1 : 0 : 1; endtable endprimitive",
       }) {
    SCOPED_TRACE(source);
    const auto result = parseWithDiagnostics(source);
    for (const auto& warning : result.warnings) {
      ADD_FAILURE() << warning.code << ": " << warning.message;
    }
    for (const auto& line : result.lines) {
      EXPECT_FALSE(line.is_opaque);
    }
  }
}

TEST_F(TreeUnwrapperTest, CovergroupDirectivesPauseGrammarAndResume) {
  const auto result = parseWithDiagnostics(
      "module m;\n"
      "  covergroup cg;\n"
      "`ifdef USE_A\n"
      "    a: coverpoint x;\n"
      "`else\n"
      "    b: coverpoint y;\n"
      "`endif\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(result.warnings.empty());
  size_t directives = 0;
  for (const auto& line : result.lines) {
    EXPECT_FALSE(line.is_opaque);
    if (!line.tokens.empty() && line.tokens.front().kind == TK::Directive) {
      ++directives;
    }
  }
  EXPECT_EQ(directives, 3U);
}

TEST_F(TreeUnwrapperTest, CovergroupMacroFallbackResumesAtNextItem) {
  const auto result = parseWithDiagnostics(
      "module m;\n"
      "  covergroup cg;\n"
      "    `COVER_ITEM\n"
      "    cp: coverpoint a;\n"
      "  endgroup\n"
      "  logic b;\n"
      "endmodule\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool saw_coverpoint = false;
  bool saw_sibling = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty()) {
      saw_coverpoint |= line.tokens.front().rawText() == "cp";
      saw_sibling |= line.tokens.front().rawText() == "logic";
    }
  }
  EXPECT_TRUE(saw_coverpoint);
  EXPECT_TRUE(saw_sibling);
}

TEST_F(TreeUnwrapperTest, MalformedPropertyRecoversAtCloseOnSameLine) {
  const auto result = parseWithDiagnostics(
      "module m; property p; a |-> ; endproperty logic b; endmodule");
  EXPECT_FALSE(result.warnings.empty());
  bool saw_property_fallback = false;
  bool saw_sibling = false;
  for (const auto& line : result.lines) {
    saw_property_fallback |=
        line.is_opaque &&
        line.raw_text.find("endproperty") != std::string::npos;
    saw_sibling |=
        !line.tokens.empty() && line.tokens.front().rawText() == "logic";
  }
  EXPECT_TRUE(saw_property_fallback);
  EXPECT_TRUE(saw_sibling);
}

TEST_F(TreeUnwrapperTest, AnnexARejectsInvalidBodyOrderWithoutLosingClose) {
  struct Example {
    std::string_view source;
    std::string_view continuation;
  };
  for (const auto& example : {
           Example{"module m; global clocking cb @(posedge clk); input a; "
                   "endclocking logic b; endmodule",
                   "logic"},
           Example{
               "config cfg; default liblist lib; endconfig module m; endmodule",
               "module"},
           Example{"primitive p(out, a); output out; input a; table 0 : 0; 0 : "
                   "0 : 0; endtable endprimitive module m; endmodule",
                   "module"},
           Example{"module m; table 0 : 0; endtable logic b; endmodule",
                   "logic"},
       }) {
    SCOPED_TRACE(example.source);
    const auto result = parseWithDiagnostics(example.source);
    EXPECT_FALSE(result.warnings.empty());
    bool resumed = false;
    for (const auto& line : result.lines) {
      resumed |= !line.tokens.empty() &&
                 line.tokens.front().rawText() == example.continuation;
    }
    EXPECT_TRUE(resumed);
  }
}

TEST_F(TreeUnwrapperTest, UdpTableSymbolsUseSlangLexemes) {
  const auto valid = parseWithDiagnostics(
      "primitive p(out, a); output out; input a; table ? : x; b : 1; endtable "
      "endprimitive");
  EXPECT_TRUE(valid.warnings.empty());

  for (const std::string_view entry : {"2 : 0;", "name : 0;", "0 : z;"}) {
    SCOPED_TRACE(entry);
    const std::string source =
        "primitive p(out, a); output out; input a; table " +
        std::string(entry) + " endtable endprimitive module m; endmodule";
    const auto result = parseWithDiagnostics(source);
    EXPECT_FALSE(result.warnings.empty());
    bool resumed = false;
    for (const auto& line : result.lines) {
      resumed |=
          !line.tokens.empty() && line.tokens.front().kind == TK::ModuleKeyword;
    }
    EXPECT_TRUE(resumed);
  }
}

TEST_F(TreeUnwrapperTest, SpecifyTimingChecksUseSystemIdentifierLexemes) {
  const auto valid = parseWithDiagnostics(
      "module m; specify $setup(a, b, 1); $hold(a, b, 1); endspecify "
      "endmodule");
  EXPECT_TRUE(valid.warnings.empty());

  const auto edge = parseWithDiagnostics(
      "module m; specify $setup(edge [01] a, b, 1); endspecify endmodule");
  EXPECT_TRUE(edge.warnings.empty());

  const auto invalid = parseWithDiagnostics(
      "module m; specify $bogus(a, b, 1); endspecify logic x; endmodule");
  EXPECT_FALSE(invalid.warnings.empty());
  bool resumed = false;
  for (const auto& line : invalid.lines) {
    resumed |=
        !line.tokens.empty() && line.tokens.front().kind == TK::LogicKeyword;
  }
  EXPECT_TRUE(resumed);

  const auto invalid_edge = parseWithDiagnostics(
      "module m; specify $setup(edge [zz] a, b, 1); endspecify logic x; "
      "endmodule");
  EXPECT_FALSE(invalid_edge.warnings.empty());
}

TEST_F(TreeUnwrapperTest, AnnexANumericTerminalsUseSlangLexemes) {
  for (const std::string_view literal : {
           "8'b10x?",
           "8'o7x?",
           "8'haf?",
           "8'd42",
           "8'shFf",
           "8'h12ab_f001",
           "8'dx",
           "8'd?",
       }) {
    SCOPED_TRACE(literal);
    const std::string source =
        "module m; localparam int a = " + std::string(literal) + "; endmodule";
    const auto result = parseWithDiagnostics(source);
    for (const auto& warning : result.warnings) {
      ADD_FAILURE() << warning.code << ": " << warning.message;
    }
  }

  for (const std::string_view literal : {"8'b2", "8'o8", "8'hg", "8'dx1"}) {
    SCOPED_TRACE(literal);
    const std::string source =
        "module m; localparam int a = " + std::string(literal) +
        "; logic b; endmodule";
    const auto result = parseWithDiagnostics(source);
    EXPECT_FALSE(result.warnings.empty());
    bool resumed = false;
    for (const auto& line : result.lines) {
      resumed |=
          !line.tokens.empty() && line.tokens.front().kind == TK::LogicKeyword;
    }
    EXPECT_TRUE(resumed);
  }
}

TEST_F(TreeUnwrapperTest, UdpRecoveryKeepsOuterPrimitiveClose) {
  for (const std::string_view body : {
           "nonsense; table 0 : 0; endtable",
           "table 0 : 0;",
       }) {
    SCOPED_TRACE(body);
    const std::string source = "primitive p(out, a); output out; input a; " +
                               std::string(body) +
                               " endprimitive module m; endmodule";
    const auto result = parseWithDiagnostics(source);
    EXPECT_FALSE(result.warnings.empty());
    bool saw_primitive_close = false;
    bool saw_module = false;
    for (const auto& line : result.lines) {
      if (!line.tokens.empty()) {
        saw_primitive_close |=
            line.tokens.front().kind == TK::EndPrimitiveKeyword;
        saw_module |= line.tokens.front().kind == TK::ModuleKeyword;
      }
    }
    EXPECT_TRUE(saw_primitive_close);
    EXPECT_TRUE(saw_module);
  }
}

TEST_F(TreeUnwrapperTest, LargeAnnexABodiesUseItemScopes) {
  std::string source = "module m; covergroup cg;\n";
  for (size_t i = 0; i < 1500; ++i) {
    source += "p" + std::to_string(i) + ": coverpoint a;\n";
  }
  source += "endgroup endmodule\n";
  auto result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());

  source = "config cfg; design lib.top;\n";
  for (size_t i = 0; i < 1500; ++i) {
    source += "default liblist lib;\n";
  }
  source += "endconfig\n";
  result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());

  source = "primitive p(out, a); output out; input a; table\n";
  for (size_t i = 0; i < 1500; ++i) {
    source += "0 : 0;\n";
  }
  source += "endtable endprimitive\n";
  result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, LongPropertyDeclarationStaysOnGrammarPath) {
  std::string source = "module m; property p;\n";
  for (size_t i = 0; i < 10000; ++i) {
    source += "logic v" + std::to_string(i) + ";\n";
  }
  source += "a; endproperty endmodule\n";
  const auto result = parseWithDiagnostics(source);
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
}

TEST_F(TreeUnwrapperTest,
       SequenceDeclarationsAndExpressionShareIdentifierStart) {
  const auto result = parseWithDiagnostics(
      "module m; sequence s; item_t value; value ##1 value; endsequence "
      "endmodule");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  for (const auto& line : result.lines) {
    EXPECT_FALSE(line.is_opaque);
  }
}

TEST_F(TreeUnwrapperTest, LongSequenceDeclarationStaysOnGrammarPath) {
  std::string source = "module m; sequence s;\n";
  for (size_t i = 0; i < 10000; ++i) {
    source += "logic v" + std::to_string(i) + ";\n";
  }
  source += "a ##1 b; endsequence endmodule\n";
  const auto result = parseWithDiagnostics(source);
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
}

TEST_F(TreeUnwrapperTest, ConditionalPropertyExpressionResumesGrammar) {
  const auto result = parseWithDiagnostics(
      "module m;\n"
      "property p;\n"
      "`ifdef USE_A\n"
      "a;\n"
      "`else\n"
      "b;\n"
      "`endif\n"
      "endproperty\n"
      "endmodule\n");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
}

TEST_F(TreeUnwrapperTest, NestedConditionalSequenceResumesGrammar) {
  const auto result = parseWithDiagnostics(
      "module m;\n"
      "sequence s;\n"
      "`ifdef A\n"
      "`ifdef B\n"
      "x;\n"
      "`else\n"
      "y;\n"
      "`endif\n"
      "`else\n"
      "z;\n"
      "`endif\n"
      "endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, IncompatiblePropertyBranchesRecoverAtClose) {
  const auto result = parseWithDiagnostics(
      "module m; property p;\n"
      "`ifdef A\n"
      "a;\n"
      "`else\n"
      "logic x;\n"
      "`endif\n"
      "endproperty logic b; endmodule\n");
  EXPECT_FALSE(result.warnings.empty());
  bool resumed = false;
  for (const auto& line : result.lines) {
    resumed |= !line.tokens.empty() &&
               line.tokens.front().rawText() == "logic" &&
               line.tokens.size() > 1 && line.tokens[1].rawText() == "b";
  }
  EXPECT_TRUE(resumed);
}

TEST_F(TreeUnwrapperTest, MalformedCovergroupItemPreservesTokensAndResumes) {
  auto result = parseWithDiagnostics(
      "module m;\n"
      "  covergroup cg;\n"
      "    logic should_stay ;\n"
      "  endgroup\n"
      "  logic b;\n"
      "endmodule\n");

  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");

  bool retained_body = false;
  bool resumed = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().rawText() == "logic") {
      retained_body |=
          line.tokens.size() > 1 && line.tokens[1].rawText() == "should_stay";
      resumed |= line.tokens.size() > 1 && line.tokens[1].rawText() == "b";
    }
  }
  EXPECT_TRUE(retained_body);
  EXPECT_TRUE(resumed);
}

TEST_F(TreeUnwrapperTest, AdjacentCovergroupsUseAnnexA) {
  auto result = parseWithDiagnostics(
      "module m;\n"
      "  covergroup cg1;\n"
      "  endgroup\n"
      "\n"
      "  covergroup cg2;\n"
      "  endgroup\n"
      "endmodule\n");

  EXPECT_TRUE(result.warnings.empty());
  size_t covergroup_count = 0;
  for (const auto& line : result.lines) {
    EXPECT_FALSE(line.is_opaque);
    if (!line.tokens.empty() &&
        line.tokens.front().kind == TK::CoverGroupKeyword) {
      ++covergroup_count;
    }
  }
  EXPECT_EQ(covergroup_count, 2U);
}

TEST_F(TreeUnwrapperTest, AppendsEofWithTrailingCommentTrivia) {
  const auto lines = parse("module m;\nendmodule // tail");
  ASSERT_FALSE(lines.empty());
  const auto& eof_line = lines.back();
  ASSERT_EQ(eof_line.tokens.size(), 1U);
  EXPECT_EQ(eof_line.tokens.front().kind, TK::EndOfFile);
  bool has_comment = false;
  for (const auto& trivia : eof_line.tokens.front().trivia()) {
    has_comment |= trivia.kind == slang::parsing::TriviaKind::LineComment;
  }
  EXPECT_TRUE(has_comment);
}

TEST_F(TreeUnwrapperTest, InvalidNestedCovergroupRecoversAtOuterClose) {
  auto result = parseWithDiagnostics(
      "module m;\n"
      "  covergroup outer;\n"
      "    covergroup inner;\n"
      "    endgroup\n"
      "  endgroup\n"
      "  logic b;\n"
      "endmodule\n");

  ASSERT_EQ(result.warnings.size(), 1U);
  size_t opaque_count = 0;
  bool resumed = false;
  for (const auto& line : result.lines) {
    if (line.is_opaque) {
      ++opaque_count;
      EXPECT_NE(line.raw_text.find("covergroup inner;"), std::string::npos);
    } else if (!line.tokens.empty() &&
               line.tokens.front().rawText() == "logic") {
      resumed = true;
    }
  }
  EXPECT_EQ(opaque_count, 1U);
  EXPECT_TRUE(resumed);
}

TEST_F(TreeUnwrapperTest, ConstraintUsesAnnexAAndKeepsFollowingItems) {
  auto result = parseWithDiagnostics(
      "class c;\n"
      "  constraint rule { x inside {[0:3]}; }\n"
      "  logic should_stay ;\n"
      "endclass\n"
      "module m;\n"
      "  logic b;\n"
      "endmodule\n");

  EXPECT_TRUE(result.warnings.empty());
  bool preserved_sibling = false;
  bool resumed_module = false;
  for (const auto& line : result.lines) {
    EXPECT_FALSE(line.is_opaque);
    if (!line.tokens.empty()) {
      preserved_sibling |= line.tokens.front().rawText() == "logic";
      resumed_module |= line.tokens.front().rawText() == "module";
    }
  }
  EXPECT_TRUE(preserved_sibling);
  EXPECT_TRUE(resumed_module);
}

TEST_F(TreeUnwrapperTest, LongConstraintBlockStaysOnGrammarPath) {
  std::string source = "class c; constraint r {\n";
  for (size_t i = 0; i < 10000; ++i) {
    source += "x" + std::to_string(i) + " > 0;\n";
  }
  source += "} endclass\n";
  const auto result = parseWithDiagnostics(source);
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
}

TEST_F(TreeUnwrapperTest, ConstraintItemsAndDirectivesResumeAtOuterClose) {
  const auto valid = parseWithDiagnostics(
      "class c; constraint r {\n"
      "`ifdef A\n"
      "if (a) { x > 0; y > 0; }\n"
      "`else\n"
      "x > 1;\n"
      "`endif\n"
      "z > 0;\n"
      "} endclass");
  EXPECT_TRUE(valid.warnings.empty());

  const auto invalid = parseWithDiagnostics(
      "class c; constraint r { nonsense ?; x > 0; } endclass module m; "
      "endmodule");
  EXPECT_FALSE(invalid.warnings.empty());
  bool resumed = false;
  for (const auto& line : invalid.lines) {
    resumed |=
        !line.tokens.empty() && line.tokens.front().kind == TK::ModuleKeyword;
  }
  EXPECT_TRUE(resumed);

  const auto missing_close = parseWithDiagnostics(
      "class c; constraint r { x > 0; endclass module m; endmodule");
  EXPECT_FALSE(missing_close.warnings.empty());
  resumed = false;
  for (const auto& line : missing_close.lines) {
    resumed |=
        !line.tokens.empty() && line.tokens.front().kind == TK::ModuleKeyword;
  }
  EXPECT_TRUE(resumed);
}

TEST_F(TreeUnwrapperTest, UnknownTextSkipsNestedBeginBeforeOuterEnd) {
  auto result = parseWithDiagnostics(
      "module m;\n"
      "  initial begin\n"
      "    ??? unknown\n"
      "    begin\n"
      "      logic inner;\n"
      "    end\n"
      "    logic still_inside;\n"
      "  end\n"
      "  logic after;\n"
      "endmodule\n");

  ASSERT_EQ(result.warnings.size(), 1U);
  bool preserved_inner_end = false;
  bool resumed_after_outer_end = false;
  for (const auto& line : result.lines) {
    if (line.is_opaque) {
      preserved_inner_end =
          line.raw_text.find("    end\n    logic still_inside;") !=
          std::string::npos;
    } else if (!line.tokens.empty() &&
               line.tokens.front().rawText() == "logic" &&
               line.tokens.size() > 1 &&
               line.tokens.at(1).rawText() == "after") {
      resumed_after_outer_end = true;
    }
  }
  EXPECT_TRUE(preserved_inner_end);
  EXPECT_TRUE(resumed_after_outer_end);
}

TEST_F(TreeUnwrapperTest, ForkJoinAnyUsesSharedBlockBoundary) {
  auto result = parseWithDiagnostics(
      "module m;\n"
      "  initial fork\n"
      "    a();\n"
      "  join_any\n"
      "  logic b;\n"
      "endmodule\n");

  EXPECT_TRUE(result.warnings.empty());
  bool resumed = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().rawText() == "logic") {
      resumed = true;
    }
  }
  EXPECT_TRUE(resumed);
}

TEST_F(TreeUnwrapperTest, AnnexARecognizesAutomaticModuleAndEndLabel) {
  const auto result =
      parseWithDiagnostics("module automatic m; logic a; endmodule : m");
  ASSERT_GE(result.lines.size(), 3U);
  EXPECT_EQ(result.lines.front().tokens.at(1).kind, TK::AutomaticKeyword);
  EXPECT_EQ(result.lines.front().tokens.at(2).rawText(), "m");
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.back().rawText(),
            "m");
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, AnnexAAttributePrefixSelectsModuleHeader) {
  const auto result =
      parseWithDiagnostics("(* keep = 1 *) module m; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  ASSERT_GE(result.lines.size(), 3U);
  EXPECT_EQ(result.lines.front().tokens.front().kind, TK::OpenParenthesis);
  EXPECT_EQ(result.lines.front().tokens.at(7).kind, TK::ModuleKeyword);
  EXPECT_EQ(result.lines[result.lines.size() - 2].tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, AnnexAHeaderIncludesPackageImportsBeforePorts) {
  const auto result = parseWithDiagnostics(
      "module m import p::*; (input logic a); logic b; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_body = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().rawText() == "logic" &&
        line.tokens.size() >= 3 && line.tokens[1].rawText() == "b" &&
        line.tokens.back().kind == TK::Semicolon) {
      found_body = true;
    }
  }
  EXPECT_TRUE(found_body);
  EXPECT_EQ(result.lines[result.lines.size() - 2].tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, ConditionalPackageItemsResumeAnnexAAfterEndif) {
  const auto result = parseWithDiagnostics(
      "package p;\n"
      "`ifdef PICK_A\n"
      "int a;\n"
      "`else\n"
      "int b;\n"
      "`endif\n"
      "int c;\n"
      "endpackage\n");
  EXPECT_TRUE(result.warnings.empty());
  bool found_after_endif = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() == 3 && line.tokens[0].kind == TK::IntKeyword &&
        line.tokens[1].rawText() == "c" &&
        line.tokens[2].kind == TK::Semicolon) {
      found_after_endif = true;
    }
  }
  EXPECT_TRUE(found_after_endif);
  EXPECT_EQ(result.lines[result.lines.size() - 2].tokens.front().kind,
            TK::EndPackageKeyword);
}

TEST_F(TreeUnwrapperTest, StandaloneMacroSkipsOnePackageItem) {
  const auto result = parseWithDiagnostics(
      "package p;\n"
      "`MAKE_TYPE\n"
      "int a;\n"
      "endpackage : p\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  EXPECT_NE(result.warnings.front().message.find("macro expansion"),
            std::string::npos);
  bool found_declaration = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() == 3 && line.tokens.front().kind == TK::IntKeyword &&
        line.tokens[1].rawText() == "a" &&
        line.tokens.back().kind == TK::Semicolon) {
      found_declaration = true;
    }
  }
  EXPECT_TRUE(found_declaration);
  EXPECT_EQ(result.lines[result.lines.size() - 2].tokens.front().kind,
            TK::EndPackageKeyword);
}

TEST_F(TreeUnwrapperTest, MacroInFunctionItemResumesAnnexABody) {
  const auto result = parseWithDiagnostics(
      "package p; class c; function int f();\n"
      "int x; x = `VALUE; return x;\n"
      "endfunction endclass endpackage\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_return = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::ReturnKeyword &&
        line.tokens.back().kind == TK::Semicolon) {
      found_return = true;
    }
  }
  EXPECT_TRUE(found_return);
  EXPECT_EQ(result.lines[result.lines.size() - 2].tokens.front().kind,
            TK::EndPackageKeyword);
}

TEST_F(TreeUnwrapperTest, MacroCaseItemResumesAtFollowingLabel) {
  const auto result = parseWithDiagnostics(
      "module m; initial case (x)\n"
      "`MAKE_CASE\n"
      "default: x = 0;\n"
      "endcase endmodule\n");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_default = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() &&
        line.tokens.front().kind == TK::DefaultKeyword &&
        line.tokens.back().kind == TK::Colon) {
      found_default = true;
    }
  }
  EXPECT_TRUE(found_default);
  EXPECT_EQ(result.lines[result.lines.size() - 3].tokens.front().kind,
            TK::EndCaseKeyword);
}

TEST_F(TreeUnwrapperTest, MacroWithoutSemicolonLeavesOuterCloseUnread) {
  const auto result =
      parseWithDiagnostics("module m; initial begin `UNKNOWN end endmodule");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  ASSERT_GE(result.lines.size(), 5U);
  EXPECT_EQ(result.lines[result.lines.size() - 3].tokens.front().kind,
            TK::EndKeyword);
  EXPECT_EQ(result.lines[result.lines.size() - 2].tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, AttributedMacroLeavesNextPackageItemUnread) {
  const auto result = parseWithDiagnostics(
      "package p; (* keep = 1 *) `UNKNOWN\nint a; endpackage");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_declaration = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() == 3 && line.tokens.front().kind == TK::IntKeyword &&
        line.tokens[1].rawText() == "a") {
      found_declaration = true;
    }
  }
  EXPECT_TRUE(found_declaration);
}

TEST_F(TreeUnwrapperTest, UniquePrefixSelectsAnnexAIfAndCase) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin "
      "unique if (a) b = 1; else b = 2; "
      "unique case (a) 0: b = 3; default: b = 4; endcase "
      "end endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_if = false;
  bool found_case = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() >= 2 &&
        line.tokens.front().kind == TK::UniqueKeyword) {
      found_if |= line.tokens[1].kind == TK::IfKeyword;
      found_case |= line.tokens[1].kind == TK::CaseKeyword;
    }
  }
  EXPECT_TRUE(found_if);
  EXPECT_TRUE(found_case);
}

TEST_F(TreeUnwrapperTest, DoWhileCompletesAsOneAnnexALoop) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin do a = a + 1; while (a < 3); end endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_tail = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::WhileKeyword &&
        line.tokens.back().kind == TK::Semicolon) {
      found_tail = true;
    }
  }
  EXPECT_TRUE(found_tail);
}

TEST_F(TreeUnwrapperTest, ProceduralAndGenerateForHeadersFollowAnnexA) {
  const auto result = parseWithDiagnostics(
      "module m; "
      "initial for (int i = 0; i < 2; i++) a[i] = 0; "
      "generate for (genvar g = 0; g < 2; g++) begin : each "
      "logic x; end endgenerate endmodule");
  EXPECT_TRUE(result.warnings.empty());
  size_t for_headers = 0;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::ForKeyword &&
        line.tokens.back().kind == TK::CloseParenthesis) {
      ++for_headers;
    }
  }
  EXPECT_EQ(for_headers, 2U);
}

TEST_F(TreeUnwrapperTest, ForHeaderNestedCallsDoNotEndAtInnerParen) {
  const auto result = parseWithDiagnostics(
      "module m; initial for (int unsigned i = 0; "
      "i < $bits(type_t); ++i) begin end endmodule");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_header = false;
  for (const auto& line : result.lines) {
    found_header |= !line.tokens.empty() &&
                    line.tokens.front().kind == TK::ForKeyword &&
                    line.tokens.back().kind == TK::CloseParenthesis;
  }
  EXPECT_TRUE(found_header);
}

TEST_F(TreeUnwrapperTest, CaseInsideAndMatchesUseAnnexAItems) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin "
      "case (a) inside [1:3]: b = 1; default: b = 0; endcase "
      "case (a) matches 1: b = 2; default: b = 0; endcase "
      "end endmodule");
  EXPECT_TRUE(result.warnings.empty());
  size_t modified_case_headers = 0;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::CaseKeyword &&
        (line.tokens.back().kind == TK::InsideKeyword ||
         line.tokens.back().kind == TK::MatchesKeyword)) {
      ++modified_case_headers;
    }
  }
  EXPECT_EQ(modified_case_headers, 2U);
}

TEST_F(TreeUnwrapperTest, IncompleteAutomaticModuleUsesDiagnosticRecovery) {
  const auto result = parseWithDiagnostics("module automatic m; logic a;");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  EXPECT_EQ(result.lines.front().tokens.at(1).kind, TK::AutomaticKeyword);
  EXPECT_EQ(result.lines.front().tokens.at(2).rawText(), "m");
}

TEST_F(TreeUnwrapperTest, AnnexABodyRuleFallbackResumesAtNextItem) {
  const auto result = parseWithDiagnostics(
      "module m(input logic a); output logic b; logic c; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool resumed = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() >= 3 && line.tokens.front().rawText() == "logic" &&
        line.tokens[1].rawText() == "c" &&
        line.tokens.back().kind == TK::Semicolon) {
      resumed = true;
    }
  }
  EXPECT_TRUE(resumed);
  EXPECT_EQ(result.lines[result.lines.size() - 2].tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, AnnexAConstructFamiliesKeepTokenOrder) {
  const std::vector<std::string_view> sources = {
      "interface bus(input logic clk); logic ready; endinterface : bus",
      "package p; parameter int N = 2; endpackage : p",
      "module m(input logic clk, output logic q); child u(.clk(clk)); "
      "always_ff @(posedge clk) begin if (clk) q <= 1; else q <= 0; end "
      "endmodule",
      "module m; generate if (1) begin : g logic a; end endgenerate "
      "endmodule",
      "module m; initial begin for (int i = 0; i < 2; i++) a[i] = 0; "
      "case (a) 0: a = 1; default: a = 2; endcase end endmodule",
      "class c; function int f(); return 1; endfunction "
      "task t(); int a; a = 1; endtask endclass",
      "module m; `define VALUE 1\n logic a; `ifdef FLAG\n assign a = `VALUE; "
      "`else\n assign a = 0; `endif\n endmodule",
  };
  for (const auto source : sources) {
    SCOPED_TRACE(source);
    const auto result = parseWithDiagnostics(source);
    EXPECT_FALSE(result.lines.empty());
    EXPECT_FALSE(std::any_of(result.warnings.begin(), result.warnings.end(),
                             [](const auto& warning) {
                               return warning.code ==
                                      "token-conservation-fallback";
                             }));
  }
}

TEST_F(TreeUnwrapperTest, NestedNamedBlocksHaveGrammarCloseLines) {
  const auto lines = parse(
      "package p; class c; function int f(); return 1; endfunction "
      "task t(); int a; a = 1; endtask endclass endpackage");
  const std::vector<TK> expected_starts = {
      TK::PackageKeyword,  TK::ClassKeyword,       TK::FunctionKeyword,
      TK::ReturnKeyword,   TK::EndFunctionKeyword, TK::TaskKeyword,
      TK::IntKeyword,      TK::Identifier,         TK::EndTaskKeyword,
      TK::EndClassKeyword, TK::EndPackageKeyword,
  };
  std::vector<TK> actual_starts;
  for (const auto& line : lines) {
    if (!line.tokens.empty() && line.tokens.front().kind != TK::EndOfFile) {
      actual_starts.push_back(line.tokens.front().kind);
    }
  }
  EXPECT_EQ(actual_starts, expected_starts);
}

TEST_F(TreeUnwrapperTest, CaseAndLoopEndAtGrammarBoundaries) {
  const auto lines = parse(
      "module m; initial begin for (int i = 0; i < 2; i++) a[i] = 0; "
      "case (a) 0: a = 1; default: a = 2; endcase end endmodule");
  std::vector<TK> starts;
  for (const auto& line : lines) {
    if (!line.tokens.empty() && line.tokens.front().kind != TK::EndOfFile) {
      starts.push_back(line.tokens.front().kind);
    }
  }
  EXPECT_NE(std::find(starts.begin(), starts.end(), TK::ForKeyword),
            starts.end());
  EXPECT_NE(std::find(starts.begin(), starts.end(), TK::CaseKeyword),
            starts.end());
  EXPECT_NE(std::find(starts.begin(), starts.end(), TK::EndCaseKeyword),
            starts.end());
  EXPECT_EQ(starts.back(), TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, AnnexACaseSeparatorFollowsCompleteExpression) {
  const auto result = parseWithDiagnostics(
      "module m; initial case (x) a ? b : c: y = 1; endcase endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_label = false;
  bool found_body = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) continue;
    if (line.tokens.front().rawText() == "a") {
      found_label =
          line.tokens.size() == 6 && line.tokens.back().kind == TK::Colon;
    }
    if (line.tokens.front().rawText() == "y") {
      found_body = line.tokens.back().kind == TK::Semicolon;
    }
  }
  EXPECT_TRUE(found_label);
  EXPECT_TRUE(found_body);
}

TEST_F(TreeUnwrapperTest, LongModuleUsesGrammarItemsWithoutTokenCutoff) {
  std::string source = "module m;\n";
  for (size_t i = 0; i < 700; ++i) {
    source += "logic a" + std::to_string(i) + ";\n";
  }
  source += "endmodule\n";
  const auto result = parseWithDiagnostics(source);
  EXPECT_GE(result.lines.size(), 702U);
  EXPECT_TRUE(std::none_of(
      result.warnings.begin(), result.warnings.end(), [](const auto& warning) {
        return warning.code == "annex-a-fallback" ||
               warning.code == "token-conservation-fallback";
      }));
}

TEST_F(TreeUnwrapperTest, LongAttributedModuleUsesGrammarItems) {
  std::string source = "(* keep = 1 *) module m;\n";
  for (size_t i = 0; i < 5000; ++i) {
    source += "int a" + std::to_string(i) + ";\n";
  }
  source += "endmodule\n";
  const auto result = parseWithDiagnostics(source);
  EXPECT_GE(result.lines.size(), 5002U);
  EXPECT_TRUE(std::none_of(
      result.warnings.begin(), result.warnings.end(), [](const auto& warning) {
        return warning.code == "annex-a-fallback" ||
               warning.code == "token-conservation-fallback";
      }));
}

TEST_F(TreeUnwrapperTest, LongPackageUsesGrammarItemsWithoutTokenCutoff) {
  std::string source = "package p;\n";
  for (size_t i = 0; i < 5000; ++i) {
    source += "int a" + std::to_string(i) + ";\n";
  }
  source += "endpackage\n";
  const auto result = parseWithDiagnostics(source);
  EXPECT_GE(result.lines.size(), 5002U);
  EXPECT_TRUE(std::none_of(
      result.warnings.begin(), result.warnings.end(), [](const auto& warning) {
        return warning.code == "annex-a-fallback" ||
               warning.code == "token-conservation-fallback";
      }));
}

TEST_F(TreeUnwrapperTest, LongNamedBodiesUsePerItemGrammar) {
  std::string source = "virtual class c;\n";
  for (size_t i = 0; i < 5000; ++i) {
    source += "int a" + std::to_string(i) + ";\n";
  }
  source += "endclass\nmodule m; function int f();\n";
  for (size_t i = 0; i < 5000; ++i) {
    source += "a = " + std::to_string(i) + ";\n";
  }
  source += "endfunction endmodule\n";
  const auto result = parseWithDiagnostics(source);
  EXPECT_GE(result.lines.size(), 10006U);
  EXPECT_TRUE(std::none_of(
      result.warnings.begin(), result.warnings.end(), [](const auto& warning) {
        return warning.code == "annex-a-fallback" ||
               warning.code == "token-conservation-fallback";
      }));
}

TEST_F(TreeUnwrapperTest, PackageTimeunitsRemainAnnexAItems) {
  const auto result =
      parseWithDiagnostics("package p; timeunit 1ns / 1ps; int a; endpackage");
  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(result.lines[result.lines.size() - 2].tokens.front().kind,
            TK::EndPackageKeyword);
}

TEST_F(TreeUnwrapperTest, PackageItemAttributeUsesAnnexAPrefix) {
  const auto result =
      parseWithDiagnostics("package p; (* keep = 1 *) int a; endpackage");
  EXPECT_TRUE(result.warnings.empty());
  bool found_attributed_item = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() &&
        line.tokens.front().kind == TK::OpenParenthesis &&
        line.tokens.back().kind == TK::Semicolon) {
      found_attributed_item = true;
    }
  }
  EXPECT_TRUE(found_attributed_item);
}

TEST_F(TreeUnwrapperTest, AttributedPackageClassAndInterfaceClassUseBodyRules) {
  const auto result = parseWithDiagnostics(
      "package p; (* keep = 1 *) class c; int x; endclass endpackage "
      "interface class ic; pure virtual function int f(); endclass");
  EXPECT_TRUE(result.warnings.empty());
  size_t endclasses = 0;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() &&
        line.tokens.front().kind == TK::EndClassKeyword) {
      ++endclasses;
    }
  }
  EXPECT_EQ(endclasses, 2U);
}

TEST_F(TreeUnwrapperTest, FunctionDeclarationsStopAtFirstStatement) {
  const auto result = parseWithDiagnostics(
      "module m; function int f(); int a; return a; int b; "
      "endfunction endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  EXPECT_EQ(result.lines[result.lines.size() - 3].tokens.front().kind,
            TK::EndFunctionKeyword);
}

TEST_F(TreeUnwrapperTest, GenerateLabelsStayWithTheirBlockKeywords) {
  const auto result = parseWithDiagnostics(
      "module m; generate if (1) begin : g logic a; end : g "
      "else begin : h logic b; end : h endgenerate endmodule");
  for (const auto& label : {"g", "h"}) {
    bool found = false;
    for (const auto& line : result.lines) {
      if (line.tokens.size() >= 3 && line.tokens[0].kind == TK::BeginKeyword &&
          line.tokens[1].kind == TK::Colon &&
          line.tokens[2].rawText() == label) {
        found = true;
      }
    }
    EXPECT_TRUE(found) << label;
  }
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, GrammarTimingControlKeepsSimpleAlwaysLine) {
  const auto lines = parse("module m; always #5 clk = ~clk; endmodule");
  ASSERT_GE(lines.size(), 3U);
  EXPECT_EQ(lines[1].tokens.front().kind, TK::AlwaysKeyword);
  EXPECT_EQ(lines[1].tokens.back().kind, TK::Semicolon);
}

TEST_F(TreeUnwrapperTest, RepeatEventControlSharesBeginHeader) {
  const auto lines = parse(
      "module m; initial begin repeat (2) @(posedge clk) begin end "
      "$display(\"done\"); end endmodule");
  bool found = false;
  for (const auto& line : lines) {
    if (line.tokens.size() >= 2 &&
        line.tokens.front().kind == TK::RepeatKeyword) {
      found = line.tokens.back().kind == TK::BeginKeyword;
    }
  }
  EXPECT_TRUE(found);
}

// NOLINTEND(misc-use-internal-linkage,bugprone-throwing-static-initialization,cert-err58-cpp,cppcoreguidelines-owning-memory,modernize-use-trailing-return-type)
