#include <gtest/gtest.h>
#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

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
  PP policy = PP::kAlwaysExpand;
  auto operator==(const LineSnap&) const -> bool = default;
};

// Converters from real lines to snapshots.

auto snap(const slang::parsing::Token& t) -> TokSnap {
  return {.kind = t.kind, .text = std::string(t.rawText())};
}

auto snap(const Line& l) -> LineSnap {
  LineSnap s{.indent = l.indentation_spaces, .policy = l.partition_policy};
  for (const auto& token : l.tokens) {
    s.tokens.push_back(snap(token));
  }
  return s;
}

auto snap(const std::vector<Line>& lines) -> std::vector<LineSnap> {
  std::vector<LineSnap> result;
  result.reserve(lines.size());
  for (const auto& l : lines) {
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
  return {.tokens = std::move(tokens), .indent = indent, .policy = policy};
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
  os << "{indent=" << line.indent << ", policy=" << policyName(line.policy)
     << ", tokens=";
  ::testing::internal::UniversalPrint(line.tokens, &os);
  return os << "}";
}

// ---------------------------------------------------------------------------
// Fixture — keeps LexContext alive so token memory outlives UnwrappedLine.
// GTest creates a fresh instance per TEST_F, so no shared state between tests.
// ---------------------------------------------------------------------------

class TreeUnwrapperTest : public ::testing::Test {
 protected:
  auto parse(std::string_view src) -> std::vector<Line> {
    tokens_ = ctx_.lex_string(src);
    const format::FormatStyle style = {.column_limit = kColumnLimit,
                                       .indentation_spaces = kIndent};
    return format::TreeUnwrapper(tokens_, style).unwrap();
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
      L(kIndent, PP::kAlwaysExpand,
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
      L(kIndent, PP::kAlwaysExpand,
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
      L(kIndent, PP::kAlwaysExpand,
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
      L(kIndent, PP::kAlwaysExpand,
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
      L(kIndent, PP::kAlwaysExpand,
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
      L(kIndent, PP::kAlwaysExpand,
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
      L(kIndent, PP::kAlwaysExpand,
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

// NOLINTEND(misc-use-internal-linkage,bugprone-throwing-static-initialization,cert-err58-cpp,cppcoreguidelines-owning-memory,modernize-use-trailing-return-type)
