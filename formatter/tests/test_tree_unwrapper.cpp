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
constexpr size_t kLongExpressionTerms = 1000;
constexpr size_t kLargeBodyItems = 1500;
constexpr size_t kVeryLargeBodyItems = 10000;
constexpr int kRepeatedItems = 120;
constexpr size_t kManyModuleItems = 700;
constexpr size_t kLongBodyItems = 5000;
constexpr size_t kCaseLabelTokens = 6;

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
        EXPECT_EQ(token.kind, tokens_.at(index).kind);
        EXPECT_EQ(token.rawText(), tokens_.at(index).rawText());
        EXPECT_EQ(token.location(), tokens_.at(index).location());
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

TEST_F(TreeUnwrapperTest, IdentifierLedItemsUseViableAnnexProductions) {
  const auto result = parseWithDiagnostics(
      "module m; type_t v; child u(a, b); child u2[2](a); "
      "initial begin v = a; end endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool saw_declaration = false;
  bool saw_instance_list = false;
  bool saw_assignment = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty() || line.is_opaque) {
      continue;
    }
    saw_declaration |= line.tokens.front().rawText() == "type_t" &&
                       line.tokens.back().kind == TK::Semicolon;
    saw_instance_list |= line.tokens.front().rawText() == "child" &&
                         line.tokens.back().kind == TK::OpenParenthesis;
    saw_assignment |= line.tokens.front().rawText() == "v" &&
                      line.tokens.back().kind == TK::Semicolon;
  }
  EXPECT_TRUE(saw_declaration);
  EXPECT_TRUE(saw_instance_list);
  EXPECT_TRUE(saw_assignment);
}

TEST_F(TreeUnwrapperTest, ConditionalParameterListResumesAnnexInstantiation) {
  const auto result = parseWithDiagnostics(
      "module m; child #(\n"
      "`ifdef A\n.P(1)\n`else\n.P(2)\n`endif\n"
      ") u(.a(a), .b(b)); endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool saw_instance_ports = false;
  bool saw_second_port = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty() || line.is_opaque) {
      continue;
    }
    saw_instance_ports |= line.tokens.front().kind == TK::CloseParenthesis &&
                          line.tokens.back().kind == TK::OpenParenthesis;
    saw_second_port |= line.tokens.front().kind == TK::Dot &&
                       line.tokens.size() > 1 &&
                       line.tokens.at(1).rawText() == "b";
  }
  EXPECT_TRUE(saw_instance_ports);
  EXPECT_TRUE(saw_second_port);
}

TEST_F(TreeUnwrapperTest, ConditionalModulePortListResumesAnnexHeader) {
  const auto result = parseWithDiagnostics(
      "module m(\n`ifdef A\ninput logic a\n`else\ninput logic b\n"
      "`endif\n); logic x; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool saw_body = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::LogicKeyword &&
        line.tokens.back().kind == TK::Semicolon) {
      saw_body = true;
    }
  }
  EXPECT_TRUE(saw_body);
}

TEST_F(TreeUnwrapperTest, ConditionalWholeModuleHeaderResumesAnnexGrammar) {
  const auto result = parseWithDiagnostics(
      "module m\n`ifdef A\n(input logic a)\n`else\n"
      "(input logic b)\n`endif\n; logic x; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, ConditionalFunctionHeaderResumesAnnexGrammar) {
  const auto result = parseWithDiagnostics(
      "module m; function int f\n`ifdef A\n(input int a)\n"
      "`else\n(input int b)\n`endif\n; return 0; "
      "endfunction endmodule");
  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndFunctionKeyword);
}

TEST_F(TreeUnwrapperTest, ConditionalModuleParametersResumeAnnexHeader) {
  const auto result = parseWithDiagnostics(
      "module m #(\n`ifdef A\nparameter int X = 1\n"
      "`else\nparameter int X = 2\n`endif\n)(); "
      "logic x; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, DifferentConditionalPortContinuationsRemainLive) {
  const auto result = parseWithDiagnostics(
      "module m(\n`ifdef A\ninput logic a,\n`else\n`endif\n"
      "input logic b); logic x; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool saw_close = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() &&
        line.tokens.front().kind == TK::EndModuleKeyword) {
      saw_close = true;
    }
  }
  EXPECT_TRUE(saw_close);
}

TEST_F(TreeUnwrapperTest, InvalidConditionalPortPathFallsBackAtHeader) {
  const auto result = parseWithDiagnostics(
      "module m(\n`ifdef A\ninput logic a\n`else\ninput logic b,\n"
      "`endif\n); logic x; endmodule");
  EXPECT_TRUE(std::any_of(
      result.warnings.begin(), result.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, MissingHeaderListCloseLeavesEndmoduleUnread) {
  const auto result =
      parseWithDiagnostics("module m(input logic a; logic x; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, MissingInstanceListCloseLeavesEndmoduleUnread) {
  const auto result = parseWithDiagnostics("module m; child u(a, b; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, NestedModuleOutsideBodyRuleRecoversAtOuterEnd) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin module n; endmodule "
      "int x; end endmodule");
  EXPECT_TRUE(std::any_of(
      result.warnings.begin(), result.warnings.end(), [](const auto& warning) {
        return warning.code == "annex-a-fallback" &&
               warning.message.find("outside the current Annex A body rule") !=
                   std::string::npos;
      }));
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndKeyword);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, NestedConditionalInsideCaseKeepsOuterBranchOpen) {
  const auto result = parseWithDiagnostics(
      "`ifdef OUTER\n"
      "module m; initial begin\n"
      "case (a)\n"
      "0: begin\n"
      "`ifdef INNER\n"
      "x = 1;\n"
      "`endif\n"
      "end\n"
      "1: begin y = 2; end\n"
      "endcase\n"
      "end endmodule\n"
      "`endif\n");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_second_item = false;
  bool found_endcase = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_second_item |= line.tokens.front().rawText() == "1";
    found_endcase |= line.tokens.front().kind == TK::EndCaseKeyword;
    EXPECT_FALSE(line.is_opaque);
  }
  EXPECT_TRUE(found_second_item);
  EXPECT_TRUE(found_endcase);
}

TEST_F(TreeUnwrapperTest, ConditionalUdpEntriesKeepAnnexTableState) {
  const auto result = parseWithDiagnostics(
      "primitive p(out, a); output out; input a; table\n"
      "`ifdef A\n"
      "0 : 0;\n"
      "`else\n"
      "1 : 1;\n"
      "`endif\n"
      "endtable endprimitive");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  EXPECT_TRUE(std::none_of(result.lines.begin(), result.lines.end(),
                           [](const auto& line) { return line.is_opaque; }));

  const auto missing_branch = parseWithDiagnostics(
      "primitive p(out, a); output out; input a; table\n"
      "`ifdef A\n"
      "0 : 0;\n"
      "`endif\n"
      "endtable endprimitive module m; endmodule");
  EXPECT_TRUE(std::any_of(
      missing_branch.warnings.begin(), missing_branch.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
  EXPECT_EQ(missing_branch.lines.at(missing_branch.lines.size() - 2)
                .tokens.front()
                .kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, ConditionalUdpPortsKeepAnnexBodyState) {
  const auto valid = parseWithDiagnostics(
      "primitive p(out, a);\n"
      "`ifdef A\n"
      "output out;\n"
      "`else\n"
      "output out;\n"
      "`endif\n"
      "input a; table 0 : 0; endtable endprimitive");
  for (const auto& warning : valid.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }

  const auto missing = parseWithDiagnostics(
      "primitive p(out, a);\n"
      "`ifdef A\n"
      "output out;\n"
      "`endif\n"
      "table 0 : 0; endtable endprimitive");
  EXPECT_TRUE(std::any_of(
      missing.warnings.begin(), missing.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
}

TEST_F(TreeUnwrapperTest, MissingUdpTableCloseResumesAtPrimitiveEnd) {
  const auto result = parseWithDiagnostics(
      "primitive p(out, a); output out; input a; table 0 : 0; "
      "endprimitive module m; endmodule");
  EXPECT_FALSE(result.warnings.empty());
  bool resumed_module = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty()) {
      resumed_module |= line.tokens.front().kind == TK::ModuleKeyword;
    }
  }
  EXPECT_TRUE(resumed_module);
}

TEST_F(TreeUnwrapperTest, ExternUdpDeclarationEndsAtAnnexHeader) {
  const auto result =
      parseWithDiagnostics("extern primitive p(out, a); module m; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, UdpTableMacroSuspendsAnnexEntryRule) {
  const auto result = parseWithDiagnostics(
      "primitive p(out, a); output out; input a; table\n"
      "`UDP_ROW\n"
      "0 : 0;\n"
      "endtable endprimitive");
  EXPECT_TRUE(std::any_of(
      result.warnings.begin(), result.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
  bool saw_entry = false;
  bool saw_close = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    saw_entry |= line.tokens.front().rawText() == "0";
    saw_close |= line.tokens.front().kind == TK::EndTableKeyword;
  }
  EXPECT_TRUE(saw_entry);
  EXPECT_TRUE(saw_close);
}

TEST_F(TreeUnwrapperTest, ConfigItemsResumeAnnexStateAcrossDirectives) {
  const auto result = parseWithDiagnostics(
      "config cfg;\n"
      "`ifdef A\n"
      "localparam int W = 1;\n"
      "`else\n"
      "localparam int W = 2;\n"
      "`endif\n"
      "design lib.top;\n"
      "`ifdef A\n"
      "default liblist lib;\n"
      "`else\n"
      "instance top.u use lib.foo;\n"
      "`endif\n"
      "endconfig");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  EXPECT_TRUE(std::none_of(result.lines.begin(), result.lines.end(),
                           [](const auto& line) { return line.is_opaque; }));
}

TEST_F(TreeUnwrapperTest, SequentialBlockDeclarationOrderFollowsAnnexA) {
  const auto valid = parseWithDiagnostics(
      "module m; initial begin int y; y = 1; end endmodule");
  EXPECT_TRUE(valid.warnings.empty());

  const auto invalid = parseWithDiagnostics(
      "module m; initial begin y += 1; int x; end endmodule");
  EXPECT_TRUE(std::any_of(
      invalid.warnings.begin(), invalid.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
  EXPECT_EQ(invalid.lines.at(invalid.lines.size() - 3).tokens.front().kind,
            TK::EndKeyword);
  EXPECT_EQ(invalid.lines.at(invalid.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, MissingOpeningLabelLeavesBlockCloseUnread) {
  const auto result =
      parseWithDiagnostics("module m; initial begin : end endmodule");
  EXPECT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndKeyword);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
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

TEST_F(TreeUnwrapperTest, AssertionPropertySpecUsesAnnexRule) {
  const auto valid = parseWithDiagnostics(
      "module m; assert property (@(posedge clk) disable iff (rst) "
      "a |-> b) else $error(\"bad\"); endmodule");
  EXPECT_TRUE(valid.warnings.empty());

  const auto malformed = parseWithDiagnostics(
      "module m; assert property (a |-> ) else $error(\"bad\"); "
      "endmodule module n; logic y; endmodule");
  ASSERT_FALSE(malformed.warnings.empty());
  EXPECT_EQ(malformed.warnings.front().code, "annex-a-fallback");
  bool parsed_second_module = false;
  for (const auto& line : malformed.lines) {
    if (line.tokens.size() >= 2 && !line.is_opaque &&
        line.tokens.front().kind == TK::LogicKeyword &&
        line.tokens.at(1).rawText() == "y") {
      parsed_second_module = true;
    }
  }
  EXPECT_TRUE(parsed_second_module);
}

TEST_F(TreeUnwrapperTest, ConditionalExpressionsResumeEnclosingAnnexRules) {
  const auto predicate = parseWithDiagnostics(
      "module m; initial begin if (\n"
      "`ifdef A\n"
      "a\n"
      "`else\n"
      "b\n"
      "`endif\n"
      ") q = 1; end endmodule");
  EXPECT_TRUE(predicate.warnings.empty());

  const auto property = parseWithDiagnostics(
      "module m; assert property (\n"
      "`ifdef A\n"
      "a |-> b\n"
      "`else\n"
      "c |-> d\n"
      "`endif\n"
      ") else $error(\"bad\"); endmodule");
  EXPECT_TRUE(property.warnings.empty());
}

TEST_F(TreeUnwrapperTest, ConditionalForHeaderResumesAnnexRule) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin for (int i = 0;\n"
      "`ifdef A\n"
      "i < 2\n"
      "`else\n"
      "i < 3\n"
      "`endif\n"
      "; i++) q = i; end endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool saw_for = false;
  bool saw_body = false;
  for (const auto& line : result.lines) {
    if (line.is_opaque) {
      continue;
    }
    for (const auto& token : line.tokens) {
      saw_for |= token.kind == TK::ForKeyword;
      saw_body |= token.kind == TK::Identifier && token.rawText() == "q";
    }
  }
  EXPECT_TRUE(saw_for);
  EXPECT_TRUE(saw_body);
}

TEST_F(TreeUnwrapperTest, LongBinaryExpressionStaysOnAnnexPath) {
  std::string source = "module m; logic y; assign y = a";
  for (size_t i = 1; i < kLongExpressionTerms; ++i) {
    source += " && a";
  }
  source += "; logic z; endmodule";
  const auto result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());
  bool saw_next_declaration = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() >= 2 && !line.is_opaque &&
        line.tokens.front().kind == TK::LogicKeyword &&
        line.tokens.at(1).rawText() == "z") {
      saw_next_declaration = true;
    }
  }
  EXPECT_TRUE(saw_next_declaration);
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
  for (size_t i = 0; i < kLargeBodyItems; ++i) {
    source += "p" + std::to_string(i) + ": coverpoint a;\n";
  }
  source += "endgroup endmodule\n";
  auto result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());

  source = "config cfg; design lib.top;\n";
  for (size_t i = 0; i < kLargeBodyItems; ++i) {
    source += "default liblist lib;\n";
  }
  source += "endconfig\n";
  result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());

  source = "primitive p(out, a); output out; input a; table\n";
  for (size_t i = 0; i < kLargeBodyItems; ++i) {
    source += "0 : 0;\n";
  }
  source += "endtable endprimitive\n";
  result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, LongPropertyDeclarationStaysOnGrammarPath) {
  std::string source = "module m; property p;\n";
  for (size_t i = 0; i < kVeryLargeBodyItems; ++i) {
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
  for (size_t i = 0; i < kVeryLargeBodyItems; ++i) {
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
               line.tokens.size() > 1 && line.tokens.at(1).rawText() == "b";
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
      retained_body |= line.tokens.size() > 1 &&
                       line.tokens.at(1).rawText() == "should_stay";
      resumed |= line.tokens.size() > 1 && line.tokens.at(1).rawText() == "b";
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
  for (size_t i = 0; i < kVeryLargeBodyItems; ++i) {
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

TEST_F(TreeUnwrapperTest, NestedConstraintIfAndUniqueUseChildRules) {
  const auto result = parseWithDiagnostics(
      "class c; rand int x; constraint r { "
      "if (x > 0) { x < 10; } else if (x < 0) x > -10; "
      "unique {x, [0:3]}; } endclass");
  EXPECT_TRUE(result.warnings.empty());
  expectTokenConservation(result.lines);
  bool found_if = false;
  bool found_else = false;
  bool found_unique = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_if |= line.tokens.front().kind == TK::IfKeyword;
    found_else |= line.tokens.front().kind == TK::ElseKeyword;
    found_unique |= line.tokens.front().kind == TK::UniqueKeyword;
  }
  EXPECT_TRUE(found_if);
  EXPECT_TRUE(found_else);
  EXPECT_TRUE(found_unique);
}

TEST_F(TreeUnwrapperTest, SolveBeforeUsesConstraintPrimaryLists) {
  const auto result = parseWithDiagnostics(
      "class c; rand int a, b, c; constraint order { "
      "solve a, b before c; disable soft c; c > 0; } endclass");
  EXPECT_TRUE(result.warnings.empty());
  expectTokenConservation(result.lines);
  bool found_solve = false;
  bool found_disable = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_solve |= line.tokens.front().kind == TK::SolveKeyword &&
                   line.tokens.back().kind == TK::Semicolon;
    found_disable |= line.tokens.front().kind == TK::DisableKeyword &&
                     line.tokens.back().kind == TK::Semicolon;
  }
  EXPECT_TRUE(found_solve);
  EXPECT_TRUE(found_disable);
}

TEST_F(TreeUnwrapperTest, ConstraintForeachCallsArrayAndLoopRules) {
  const auto result = parseWithDiagnostics(
      "class c; rand int a[4]; constraint r { "
      "foreach (a[i]) { a[i] > 0; } } endclass");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
  bool found_foreach = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_foreach |= line.tokens.front().kind == TK::ForeachKeyword;
  }
  EXPECT_TRUE(found_foreach);
}

TEST_F(TreeUnwrapperTest, ProceduralForeachCallsSharedHeaderRule) {
  const auto result = parseWithDiagnostics(
      "module m; int a[4]; initial foreach (a[i]) a[i] = 0; "
      "endmodule");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
  const auto empty_index = parseWithDiagnostics(
      "module m; int a[4]; initial foreach (a[]) a[0] = 0; "
      "endmodule");
  ASSERT_TRUE(empty_index.warnings.empty())
      << empty_index.warnings.front().message;
  expectTokenConservation(empty_index.lines);
}

TEST_F(TreeUnwrapperTest, ProceduralKeywordsCallTheirBodyRules) {
  const auto result = parseWithDiagnostics(
      "module m; initial ; always_comb begin x = 1; end "
      "final begin x = 2; end endmodule");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, ConstraintExpressionCallsDistAndSetRules) {
  const auto result = parseWithDiagnostics(
      "class c; rand int x; constraint r { "
      "soft x > 0; x dist {[0:3] := 1, 4 :/ 2}; "
      "(x > 0) -> x < 10; } endclass");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, ClassConstraintHeaderCallsModifierAndNameRules) {
  const auto result = parseWithDiagnostics(
      "class c; constraint : initial r { x > 0; } "
      "static constraint : final p; endclass");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, ClassConstraintHeaderResumesAfterConditional) {
  const auto result = parseWithDiagnostics(
      "class c; constraint\n"
      "`ifdef USE_A\n"
      "a\n"
      "`else\n"
      "b\n"
      "`endif\n"
      "{ x > 0; } endclass");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, ExternConstraintHeaderKeepsFinalIdentifier) {
  const auto result = parseWithDiagnostics(
      "class outer; class inner; rand int x; endclass endclass "
      "constraint outer::inner::positive { x > 0; }");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, ConstraintIfConditionResumesAfterDirective) {
  const auto result = parseWithDiagnostics(
      "class c; constraint r { if (\n"
      "`ifdef USE_X\n"
      "x\n"
      "`else\n"
      "y\n"
      "`endif\n"
      ") x > 0; } endclass");
  EXPECT_TRUE(result.warnings.empty());
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, MissingConstraintSetRecoversAtOuterBrace) {
  const auto result = parseWithDiagnostics(
      "class c; constraint r { if (x > 0) { x < 10; } else } "
      "endclass module next; endmodule");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  expectTokenConservation(result.lines);
  bool found_module = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_module |= line.tokens.front().kind == TK::ModuleKeyword;
  }
  EXPECT_TRUE(found_module);
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
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, AnnexAHeaderIncludesPackageImportsBeforePorts) {
  const auto result = parseWithDiagnostics(
      "module m import p::*; (input logic a); logic b; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_body = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().rawText() == "logic" &&
        line.tokens.size() >= 3 && line.tokens.at(1).rawText() == "b" &&
        line.tokens.back().kind == TK::Semicolon) {
      found_body = true;
    }
  }
  EXPECT_TRUE(found_body);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
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
    if (line.tokens.size() == 3 && line.tokens.at(0).kind == TK::IntKeyword &&
        line.tokens.at(1).rawText() == "c" &&
        line.tokens.at(2).kind == TK::Semicolon) {
      found_after_endif = true;
    }
  }
  EXPECT_TRUE(found_after_endif);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
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
        line.tokens.at(1).rawText() == "a" &&
        line.tokens.back().kind == TK::Semicolon) {
      found_declaration = true;
    }
  }
  EXPECT_TRUE(found_declaration);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
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
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndPackageKeyword);
}

TEST_F(TreeUnwrapperTest, MacroAfterConditionalPredicateKeepsOuterClose) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin if (\n"
      "`ifdef A\na\n`else\nb\n`endif\n"
      ") `MAKE_STMT\n"
      "x = 1; end endmodule");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  EXPECT_NE(result.warnings.front().message.find("macro expansion"),
            std::string::npos);
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndKeyword);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
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
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndCaseKeyword);
}

TEST_F(TreeUnwrapperTest, MacroWithoutSemicolonLeavesOuterCloseUnread) {
  const auto result =
      parseWithDiagnostics("module m; initial begin `UNKNOWN end endmodule");
  ASSERT_EQ(result.warnings.size(), 1U);
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  ASSERT_GE(result.lines.size(), 5U);
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndKeyword);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
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
        line.tokens.at(1).rawText() == "a") {
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
      found_if |= line.tokens.at(1).kind == TK::IfKeyword;
      found_case |= line.tokens.at(1).kind == TK::CaseKeyword;
    }
  }
  EXPECT_TRUE(found_if);
  EXPECT_TRUE(found_case);
}

TEST_F(TreeUnwrapperTest, LabeledPriorityAndUnique0CallStatementRules) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin "
      "check_a: priority if (a) begin b = 1; end else b = 2; "
      "check_b: unique0 case (a) 0: b = 3; default: b = 4; endcase "
      "end endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_priority_if = false;
  bool found_unique0_case = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() < 4 || line.tokens.at(1).kind != TK::Colon) {
      continue;
    }
    found_priority_if |= line.tokens.at(2).kind == TK::PriorityKeyword &&
                         line.tokens.at(3).kind == TK::IfKeyword;
    found_unique0_case |= line.tokens.at(2).kind == TK::Unique0Keyword &&
                          line.tokens.at(3).kind == TK::CaseKeyword;
  }
  EXPECT_TRUE(found_priority_if);
  EXPECT_TRUE(found_unique0_case);
}

TEST_F(TreeUnwrapperTest, MalformedUniquePrefixRecoversAtOuterBlock) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin unique b = 1; end logic after; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_after = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::LogicKeyword) {
      found_after = true;
    }
  }
  EXPECT_TRUE(found_after);
}

TEST_F(TreeUnwrapperTest, ModuleCommonLeafRulesKeepTheirContexts) {
  const auto result = parseWithDiagnostics(
      "module m; wire a, b, c; assign a = b; alias a = b = c; "
      "initial begin assign a = b; end endmodule "
      "program p; assign a = b; endprogram");
  EXPECT_TRUE(result.warnings.empty());
  expectTokenConservation(result.lines);
  size_t assignments = 0;
  bool found_alias = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    assignments += line.tokens.front().kind == TK::AssignKeyword;
    found_alias |= line.tokens.front().kind == TK::AliasKeyword;
  }
  EXPECT_EQ(assignments, 3U);
  EXPECT_TRUE(found_alias);
}

TEST_F(TreeUnwrapperTest, GenvarAndDefparamFinishBeforeNextModuleItem) {
  const auto result = parseWithDiagnostics(
      "module m; genvar i, j; defparam u.P = 1, v.Q = 2; "
      "logic a; endmodule");
  expectTokenConservation(result.lines);
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  std::vector<TK> starts;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind != TK::EndOfFile) {
      starts.push_back(line.tokens.front().kind);
    }
  }
  EXPECT_NE(std::find(starts.begin(), starts.end(), TK::GenVarKeyword),
            starts.end());
  EXPECT_NE(std::find(starts.begin(), starts.end(), TK::DefParamKeyword),
            starts.end());
  EXPECT_NE(std::find(starts.begin(), starts.end(), TK::LogicKeyword),
            starts.end());
}

TEST_F(TreeUnwrapperTest, MalformedAliasPreservesTokensAndNextModule) {
  const auto result = parseWithDiagnostics(
      "module m; alias a = ; endmodule module next; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  expectTokenConservation(result.lines);
  bool found_next = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() >= 2 &&
        line.tokens.front().kind == TK::ModuleKeyword &&
        line.tokens.at(1).rawText() == "next") {
      found_next = true;
    }
  }
  EXPECT_TRUE(found_next);
}

TEST_F(TreeUnwrapperTest, SpecparamUsesAnnexRuleAndResumesModuleItems) {
  const auto result = parseWithDiagnostics(
      "module m; specparam [3:0] SETUP = 2, HOLD = 3; "
      "logic ready; endmodule");
  expectTokenConservation(result.lines);
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_specparam = false;
  bool found_logic = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_specparam |= line.tokens.front().kind == TK::SpecParamKeyword &&
                       line.tokens.back().kind == TK::Semicolon;
    found_logic |= line.tokens.front().kind == TK::LogicKeyword;
  }
  EXPECT_TRUE(found_specparam);
  EXPECT_TRUE(found_logic);
}

TEST_F(TreeUnwrapperTest, TypedefUsesTypeRuleInModulePackageAndInterfaceClass) {
  const auto result = parseWithDiagnostics(
      "module m; typedef logic [3:0] word_t; word_t x; endmodule "
      "package p; typedef int value_t; endpackage "
      "interface class ic; typedef int item_t; endclass");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t typedefs = 0;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() &&
        line.tokens.front().kind == TK::TypedefKeyword) {
      ++typedefs;
    }
  }
  EXPECT_EQ(typedefs, 3U);
}

TEST_F(TreeUnwrapperTest, BuiltInDataTypesCallDeclarationRule) {
  const auto result = parseWithDiagnostics(
      "module m; logic [3:0] a; int b; "
      "struct packed { logic x; } c; "
      "function int f(); int local_value; return local_value; endfunction "
      "endmodule "
      "class cls; string name; endclass");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_logic = false;
  bool found_struct = false;
  bool found_string = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_logic |= line.tokens.front().kind == TK::LogicKeyword;
    found_struct |= line.tokens.front().kind == TK::StructKeyword;
    found_string |= line.tokens.front().kind == TK::StringKeyword;
  }
  EXPECT_TRUE(found_logic);
  EXPECT_TRUE(found_struct);
  EXPECT_TRUE(found_string);
}

TEST_F(TreeUnwrapperTest, NetTypesCallNetDeclarationRule) {
  const auto result = parseWithDiagnostics(
      "module m; wire a; tri [3:0] b; logic c; endmodule "
      "package p; uwire signal; endpackage");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_wire = false;
  bool found_tri = false;
  bool found_uwire = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_wire |= line.tokens.front().kind == TK::WireKeyword;
    found_tri |= line.tokens.front().kind == TK::TriKeyword;
    found_uwire |= line.tokens.front().kind == TK::UWireKeyword;
  }
  EXPECT_TRUE(found_wire);
  EXPECT_TRUE(found_tri);
  EXPECT_TRUE(found_uwire);
}

TEST_F(TreeUnwrapperTest, ContinuousAssignmentResumesAcrossConditional) {
  const auto result = parseWithDiagnostics(
      "module m;\n"
      "assign a = 1'b1\n"
      "`ifdef USE_B\n"
      "  & b\n"
      "`endif\n"
      ";\n"
      "assign c = d;\n"
      "endmodule\n");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t assignments = 0;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::AssignKeyword) {
      ++assignments;
    }
  }
  EXPECT_EQ(assignments, 2U);
}

TEST_F(TreeUnwrapperTest, AnsiInterfaceAndProgramItemsCallTheirRules) {
  const auto result = parseWithDiagnostics(
      "interface bus(input logic clk); assign ready = clk; "
      "initial begin ready = 1; end endinterface "
      "program p(input logic clk); assign done = clk; "
      "initial begin done = 1; end endprogram");
  EXPECT_TRUE(result.warnings.empty());
  size_t assignments = 0;
  bool found_interface_close = false;
  bool found_program_close = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    assignments += line.tokens.front().kind == TK::AssignKeyword;
    found_interface_close |=
        line.tokens.front().kind == TK::EndInterfaceKeyword;
    found_program_close |= line.tokens.front().kind == TK::EndProgramKeyword;
  }
  EXPECT_EQ(assignments, 2U);
  EXPECT_TRUE(found_interface_close);
  EXPECT_TRUE(found_program_close);
}

TEST_F(TreeUnwrapperTest, NonAnsiPortItemsUseChildAndParentRules) {
  const auto result = parseWithDiagnostics(
      "module m(a, b); input logic a; output logic b; endmodule "
      "interface bus(clk); input logic clk; endinterface "
      "program p(done); output logic done; endprogram");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t port_items = 0;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    if (line.tokens.front().kind == TK::InputKeyword ||
        line.tokens.front().kind == TK::OutputKeyword) {
      EXPECT_EQ(line.tokens.back().kind, TK::Semicolon);
      ++port_items;
    }
  }
  EXPECT_EQ(port_items, 4U);
}

TEST_F(TreeUnwrapperTest, AnsiHeaderDoesNotAdmitBodyPortDeclaration) {
  const auto result = parseWithDiagnostics(
      "module m(input logic a); input logic b; endmodule "
      "module after; logic ready; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_following_module = false;
  bool found_ready = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_following_module |=
        line.tokens.front().kind == TK::ModuleKeyword &&
        std::any_of(
            line.tokens.begin(), line.tokens.end(),
            [](const auto& token) { return token.rawText() == "after"; });
    found_ready |= line.tokens.front().kind == TK::LogicKeyword;
  }
  EXPECT_TRUE(found_following_module);
  EXPECT_TRUE(found_ready);
}

TEST_F(TreeUnwrapperTest, MissingNonAnsiPortSemicolonKeepsOuterClose) {
  const auto result = parseWithDiagnostics(
      "module m(a); input logic a endmodule "
      "module after; logic ready; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_first_close = false;
  bool found_following_module = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_first_close |= line.tokens.front().kind == TK::EndModuleKeyword;
    found_following_module |=
        line.tokens.front().kind == TK::ModuleKeyword &&
        std::any_of(
            line.tokens.begin(), line.tokens.end(),
            [](const auto& token) { return token.rawText() == "after"; });
  }
  EXPECT_TRUE(found_first_close);
  EXPECT_TRUE(found_following_module);
}

TEST_F(TreeUnwrapperTest, TaskPortDeclarationsUseTfRule) {
  const auto result = parseWithDiagnostics(
      "module m; task write; input int value; output int result; "
      "result = value; endtask logic ready; endmodule");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t port_items = 0;
  bool found_ready = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    port_items += line.tokens.front().kind == TK::InputKeyword ||
                  line.tokens.front().kind == TK::OutputKeyword;
    found_ready |= line.tokens.front().kind == TK::LogicKeyword;
  }
  EXPECT_EQ(port_items, 2U);
  EXPECT_TRUE(found_ready);
}

TEST_F(TreeUnwrapperTest, ParameterItemsUseChildAndParentRules) {
  const auto result = parseWithDiagnostics(
      "module m; parameter int WIDTH = 8; localparam int DEPTH = 2; "
      "initial begin localparam int BASE = 1; int x; end "
      "task t; parameter int ARG = 3; endtask endmodule "
      "package p; parameter type word_t = int; endpackage "
      "class c; localparam int SIZE = 4; endclass "
      "interface class ic; parameter int N = 1; endclass");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t parameter_items = 0;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    if (line.tokens.front().kind == TK::ParameterKeyword ||
        line.tokens.front().kind == TK::LocalParamKeyword) {
      EXPECT_EQ(line.tokens.back().kind, TK::Semicolon);
      ++parameter_items;
    }
  }
  EXPECT_EQ(parameter_items, 7U);
}

TEST_F(TreeUnwrapperTest, NettypeDeclarationsUseAnnexRule) {
  const auto result = parseWithDiagnostics(
      "module m; nettype logic wire_t; wire_t signal; endmodule "
      "package p; nettype int word_t; endpackage "
      "class c; nettype bit flag_t; endclass");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t nettypes = 0;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    if (line.tokens.front().kind == TK::NetTypeKeyword) {
      EXPECT_EQ(line.tokens.back().kind, TK::Semicolon);
      ++nettypes;
    }
  }
  EXPECT_EQ(nettypes, 3U);
}

TEST_F(TreeUnwrapperTest, LetDeclarationsUseBlockItemRule) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin let one = 1; int x; x = one; end "
      "task t; let two = 2; int y; y = two; endtask endmodule");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t let_items = 0;
  for (const auto& line : result.lines) {
    if (line.tokens.empty() || line.tokens.front().kind != TK::LetKeyword) {
      continue;
    }
    EXPECT_EQ(line.tokens.back().kind, TK::Semicolon);
    ++let_items;
  }
  EXPECT_EQ(let_items, 2U);
}

TEST_F(TreeUnwrapperTest, InterfaceModportAndClockingCallAnnexRules) {
  const auto result = parseWithDiagnostics(
      "interface bus(input logic clk); "
      "modport master (input clk); "
      "clocking cb @(posedge clk); input data; endclocking "
      "endinterface");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_modport = false;
  bool found_clocking = false;
  bool found_close = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_modport |= line.tokens.front().kind == TK::ModPortKeyword;
    found_clocking |= line.tokens.front().kind == TK::ClockingKeyword;
    found_close |= line.tokens.front().kind == TK::EndClockingKeyword;
  }
  EXPECT_TRUE(found_modport);
  EXPECT_TRUE(found_clocking);
  EXPECT_TRUE(found_close);
}

TEST_F(TreeUnwrapperTest, InterfaceExternMethodsUseAnnexRule) {
  const auto result = parseWithDiagnostics(
      "interface bus; extern function int read(input int index); "
      "extern forkjoin task write(input int value); "
      "logic ready; endinterface");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t extern_items = 0;
  bool found_logic = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    extern_items += line.tokens.front().kind == TK::ExternKeyword &&
                    line.tokens.back().kind == TK::Semicolon;
    found_logic |= line.tokens.front().kind == TK::LogicKeyword;
  }
  EXPECT_EQ(extern_items, 2U);
  EXPECT_TRUE(found_logic);
}

TEST_F(TreeUnwrapperTest, VirtualClassAndStaticConstraintUseDeclarationRules) {
  const auto result = parseWithDiagnostics(
      "package p; virtual class c; "
      "static constraint valid { x > 0; } "
      "virtual function int f(); return x; endfunction "
      "endclass endpackage");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_constraint = false;
  bool found_method = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() < 2) {
      continue;
    }
    found_constraint |= line.tokens.front().kind == TK::StaticKeyword &&
                        line.tokens.at(1).kind == TK::ConstraintKeyword;
    found_method |= line.tokens.front().kind == TK::VirtualKeyword &&
                    line.tokens.at(1).kind == TK::FunctionKeyword;
  }
  EXPECT_TRUE(found_constraint);
  EXPECT_TRUE(found_method);
}

TEST_F(TreeUnwrapperTest, RandomAndConstClassPropertiesUseAnnexRule) {
  const auto result = parseWithDiagnostics(
      "class c; typedef int word_t; rand int x; randc bit [1:0] y; "
      "const int z = 1; static int count; protected word_t value; "
      "local int index; "
      "static virtual function int read(); return value; endfunction "
      "endclass");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t direct_properties = 0;
  bool found_static = false;
  bool found_protected = false;
  bool found_local = false;
  bool found_method = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    direct_properties += line.tokens.front().kind == TK::RandKeyword ||
                         line.tokens.front().kind == TK::RandCKeyword ||
                         line.tokens.front().kind == TK::ConstKeyword;
    found_static |= line.tokens.front().kind == TK::StaticKeyword;
    found_protected |= line.tokens.front().kind == TK::ProtectedKeyword;
    found_local |= line.tokens.front().kind == TK::LocalKeyword;
    found_method |= std::any_of(
        line.tokens.begin(), line.tokens.end(),
        [](const auto& token) { return token.kind == TK::FunctionKeyword; });
  }
  EXPECT_EQ(direct_properties, 3U);
  EXPECT_TRUE(found_static);
  EXPECT_TRUE(found_protected);
  EXPECT_TRUE(found_local);
  EXPECT_TRUE(found_method);
}

TEST_F(TreeUnwrapperTest, PureVirtualMethodPrototypeKeepsItsSemicolon) {
  const auto result = parseWithDiagnostics(
      "virtual class c; pure virtual function int read(); endclass "
      "module after; endmodule");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_prototype = false;
  bool found_module = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_prototype |= line.tokens.front().kind == TK::PureKeyword &&
                       line.tokens.back().kind == TK::Semicolon;
    found_module |= line.tokens.front().kind == TK::ModuleKeyword;
  }
  EXPECT_TRUE(found_prototype);
  EXPECT_TRUE(found_module);
}

TEST_F(TreeUnwrapperTest, ExternClassMethodsUsePrototypeProduction) {
  const auto result = parseWithDiagnostics(
      "class c; extern function int read(input int x); "
      "extern task write(input int x); "
      "constraint positive { x > 0; } endclass");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t extern_methods = 0;
  bool found_constraint = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    extern_methods += line.tokens.front().kind == TK::ExternKeyword &&
                      line.tokens.back().kind == TK::Semicolon;
    found_constraint |= line.tokens.front().kind == TK::ConstraintKeyword;
  }
  EXPECT_EQ(extern_methods, 2U);
  EXPECT_TRUE(found_constraint);
}

TEST_F(TreeUnwrapperTest, ConstraintPrototypesUseAnnexProduction) {
  const auto result = parseWithDiagnostics(
      "class c; int x; extern constraint positive; endclass "
      "constraint c::positive { x > 0; } "
      "virtual class d; pure constraint valid; endclass "
      "class e; static constraint valid; endclass "
      "class f; constraint implicit; endclass "
      "module after; endmodule");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t prototypes = 0;
  bool found_external_definition = false;
  bool found_following_module = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    prototypes += line.tokens.back().kind == TK::Semicolon &&
                  (line.tokens.front().kind == TK::ExternKeyword ||
                   line.tokens.front().kind == TK::PureKeyword ||
                   line.tokens.front().kind == TK::StaticKeyword ||
                   line.tokens.front().kind == TK::ConstraintKeyword);
    found_external_definition |=
        line.tokens.front().kind == TK::ConstraintKeyword &&
        line.tokens.back().kind == TK::OpenBrace;
    found_following_module |= line.tokens.front().kind == TK::ModuleKeyword;
  }
  EXPECT_EQ(prototypes, 4U);
  EXPECT_TRUE(found_external_definition);
  EXPECT_TRUE(found_following_module);
}

TEST_F(TreeUnwrapperTest, ScopedConstraintUsesExternConstraintProduction) {
  const auto result = parseWithDiagnostics(
      "package p; class c; int x; endclass "
      "constraint c::positive { x > 0; } "
      "localparam int READY = 1; endpackage");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  bool found_constraint = false;
  bool found_parameter = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_constraint |= line.tokens.front().kind == TK::ConstraintKeyword;
    found_parameter |= line.tokens.front().kind == TK::LocalParamKeyword;
  }
  EXPECT_TRUE(found_constraint);
  EXPECT_TRUE(found_parameter);
}

TEST_F(TreeUnwrapperTest, BindRuleFailureRecoversAtModuleClose) {
  const auto result = parseWithDiagnostics(
      "module m; bind m child u(); endmodule "
      "program p; assign a = b; endprogram");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_program = false;
  bool found_assignment = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_program |= line.tokens.front().kind == TK::ProgramKeyword;
    found_assignment |= line.tokens.front().kind == TK::AssignKeyword;
  }
  EXPECT_TRUE(found_program);
  EXPECT_TRUE(found_assignment);
}

TEST_F(TreeUnwrapperTest, AssertPropertyHeaderRecoversAtModuleClose) {
  const auto result = parseWithDiagnostics(
      "module broken; assert property a; endmodule "
      "module next; assert property (b); endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_next = false;
  bool found_assert = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_next |= line.tokens.front().kind == TK::ModuleKeyword &&
                  line.tokens.size() > 1 &&
                  line.tokens.at(1).rawText() == "next";
    found_assert |= line.tokens.front().kind == TK::AssertKeyword &&
                    line.tokens.size() > 1 &&
                    line.tokens.at(1).kind == TK::PropertyKeyword;
  }
  EXPECT_TRUE(found_next);
  EXPECT_TRUE(found_assert);
}

TEST_F(TreeUnwrapperTest, RepeatedCaseBlocksKeepAnnexAItemsIndependent) {
  std::string source = "module m; always_comb begin case (sel) ";
  for (int i = 0; i < kRepeatedItems; ++i) {
    source +=
        std::to_string(i) + ": begin value = " + std::to_string(i) + "; end ";
  }
  source += "endcase end endmodule";

  const auto result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());
  size_t case_items = 0;
  for (const auto& line : result.lines) {
    if (line.tokens.size() >= 2 &&
        line.tokens.front().kind == TK::IntegerLiteral &&
        line.tokens.at(1).kind == TK::Colon) {
      ++case_items;
    }
  }
  EXPECT_EQ(case_items, 120U);
}

TEST_F(TreeUnwrapperTest, NestedCaseBodyResumesAtNextAnnexAItem) {
  const auto result = parseWithDiagnostics(
      "module m; always_comb begin case (sel) "
      "0: begin for (int unsigned i = 0; i < N; ++i) begin "
      "if (a) begin x = i; end end end "
      "1: begin y = 1; end endcase end endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_next_item = false;
  for (const auto& line : result.lines) {
    found_next_item |= line.tokens.size() >= 2 &&
                       line.tokens.front().rawText() == "1" &&
                       line.tokens.at(1).kind == TK::Colon;
  }
  EXPECT_TRUE(found_next_item);
}

TEST_F(TreeUnwrapperTest, NestedCaseAcrossDirectiveKeepsItemBoundaries) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin case (a) 0: begin\n"
      "`ifdef X\ncase (b)\n1: x = 1;\n2: x = 2;\nendcase\n`endif\n"
      "end endcase end endmodule");
  size_t case_headers = 0;
  size_t case_items = 0;
  size_t case_closes = 0;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    case_headers += line.tokens.front().kind == TK::CaseKeyword;
    case_items += line.tokens.size() >= 2 &&
                  line.tokens.at(0).kind == TK::IntegerLiteral &&
                  line.tokens.at(1).kind == TK::Colon;
    case_closes += line.tokens.front().kind == TK::EndCaseKeyword;
  }
  EXPECT_EQ(case_headers, 2U);
  EXPECT_EQ(case_items, 3U);
  EXPECT_EQ(case_closes, 2U);
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, ConditionalCaseAlternativeWithNestedDirective) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin case (sel)\n"
      "`ifdef A\n0: x = 0;\ndefault: begin\n"
      "`ifdef B\ny = 1;\n`endif\nend\n"
      "`else\ndefault: begin y = 2; end\n`endif\n"
      "endcase end endmodule");
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, ConditionalCaseLabelResumesSameAnnexRule) {
  const auto result = parseWithDiagnostics(
      "module m; initial case (sel) 1\n"
      "`ifdef A\n+ 1\n`else\n+ 2\n`endif\n"
      ": x = 1; endcase endmodule");
  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, RandcaseUsesAnnexAItems) {
  const auto result = parseWithDiagnostics(
      "module m; initial randcase 1: a = 0; "
      "2: begin b = 1; end endcase endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_randcase = false;
  bool found_endcase = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_randcase |= line.tokens.front().kind == TK::RandCaseKeyword;
    found_endcase |= line.tokens.front().kind == TK::EndCaseKeyword;
  }
  EXPECT_TRUE(found_randcase);
  EXPECT_TRUE(found_endcase);
}

TEST_F(TreeUnwrapperTest, RandsequenceCallsProductionRulePerItem) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin logic done; "
      "randsequence (root) root : leaf; leaf : root; endsequence "
      "done = 1; end endmodule");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t production_items = 0;
  bool found_close = false;
  bool found_done = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    production_items +=
        line.tokens.front().kind == TK::Identifier &&
        line.tokens.back().kind == TK::Semicolon &&
        std::any_of(line.tokens.begin(), line.tokens.end(),
                    [](const auto& token) { return token.kind == TK::Colon; });
    found_close |= line.tokens.front().kind == TK::EndSequenceKeyword;
    found_done |= line.tokens.front().kind == TK::LogicKeyword;
  }
  EXPECT_EQ(production_items, 2U);
  EXPECT_TRUE(found_close);
  EXPECT_TRUE(found_done);
}

TEST_F(TreeUnwrapperTest, RandsequenceResumesProductionsAcrossDirective) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin\n"
      "randsequence (root)\n"
      "root : leaf;\n"
      "`ifdef EXTRA\n"
      "extra : leaf;\n"
      "`endif\n"
      "leaf : root;\n"
      "endsequence\n"
      "end endmodule\n");
  for (const auto& warning : result.warnings) {
    ADD_FAILURE() << warning.code << ": " << warning.message;
  }
  size_t productions = 0;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::Identifier &&
        std::any_of(
            line.tokens.begin(), line.tokens.end(),
            [](const auto& token) { return token.kind == TK::Colon; })) {
      ++productions;
    }
  }
  EXPECT_EQ(productions, 3U);
}

TEST_F(TreeUnwrapperTest, MalformedRandsequenceKeepsOuterEnd) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin randsequence (root root : leaf; "
      "endsequence end logic ready; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  bool found_end = false;
  bool found_ready = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_end |= line.tokens.front().kind == TK::EndKeyword;
    found_ready |= line.tokens.front().kind == TK::LogicKeyword;
  }
  EXPECT_TRUE(found_end);
  EXPECT_TRUE(found_ready);
}

TEST_F(TreeUnwrapperTest, EmptyCaseReportsAnnexARuleFailure) {
  const auto result =
      parseWithDiagnostics("module m; initial case (a) endcase endmodule");
  EXPECT_TRUE(std::any_of(
      result.warnings.begin(), result.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndCaseKeyword);
}

TEST_F(TreeUnwrapperTest, MalformedCaseItemRecoversAfterEndcase) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin case (a) 0 b = 1; endcase "
      "y = 2; end endmodule");
  EXPECT_TRUE(std::any_of(
      result.warnings.begin(), result.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
  bool found_tail = false;
  for (const auto& line : result.lines) {
    found_tail |= !line.tokens.empty() && line.tokens.front().rawText() == "y";
  }
  EXPECT_TRUE(found_tail);
  EXPECT_FALSE(std::any_of(
      result.warnings.begin(), result.warnings.end(), [](const auto& warning) {
        return warning.code == "token-conservation-fallback";
      }));
}

TEST_F(TreeUnwrapperTest, GenerateRegionParsesRepeatedAnnexAItems) {
  std::string source = "module m; generate ";
  for (int i = 0; i < kRepeatedItems; ++i) {
    source += "wire w" + std::to_string(i) + "; ";
  }
  source += "endgenerate endmodule";
  const auto result = parseWithDiagnostics(source);
  EXPECT_TRUE(result.warnings.empty());
  size_t declarations = 0;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() && line.tokens.front().kind == TK::WireKeyword) {
      ++declarations;
    }
  }
  EXPECT_EQ(declarations, 120U);
}

TEST_F(TreeUnwrapperTest, DescriptionCallsNestedModuleAndGenerateRules) {
  const auto result = parseWithDiagnostics(
      "module automatic outer; "
      "macromodule inner; endmodule : inner "
      "generate wire x; endgenerate "
      "endmodule : outer");
  EXPECT_TRUE(result.warnings.empty());
  size_t module_headers = 0;
  bool found_generate = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    module_headers += line.tokens.front().kind == TK::ModuleKeyword ||
                      line.tokens.front().kind == TK::MacromoduleKeyword;
    found_generate |= line.tokens.front().kind == TK::GenerateKeyword;
  }
  EXPECT_EQ(module_headers, 2U);
  EXPECT_TRUE(found_generate);
}

TEST_F(TreeUnwrapperTest, ProceduralAndGenerateIfCallDifferentBodyRules) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin "
      "if (a) x = 1; else if (b) x = 2; else x = 3; end "
      "generate if (1) begin : yes wire y; end : yes "
      "else begin : no wire n; end : no endgenerate endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool found_else_if = false;
  bool found_generate_body = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    found_else_if |= line.tokens.size() >= 2 &&
                     line.tokens.front().kind == TK::ElseKeyword &&
                     line.tokens.at(1).kind == TK::IfKeyword;
    for (size_t i = 1; i < line.tokens.size(); ++i) {
      found_generate_body |= line.tokens.at(i - 1).kind == TK::WireKeyword &&
                             line.tokens.at(i).rawText() == "n";
    }
  }
  EXPECT_TRUE(found_else_if);
  EXPECT_TRUE(found_generate_body);
}

TEST_F(TreeUnwrapperTest, GenerateBlockRuleCallsNestedItemRules) {
  const auto result = parseWithDiagnostics(
      "module m; if (1) g: begin : body "
      "for (genvar i = 0; i < 2; i++) begin : item wire x; end : item "
      "case (1) 1: begin : choice wire y; end : choice endcase "
      "end : body endmodule");
  EXPECT_TRUE(result.warnings.empty());
  size_t begin_count = 0;
  size_t end_count = 0;
  for (const auto& line : result.lines) {
    if (line.tokens.empty()) {
      continue;
    }
    begin_count += line.tokens.front().kind == TK::BeginKeyword ||
                   (line.tokens.front().kind == TK::Identifier &&
                    line.tokens.front().rawText() == "g");
    end_count += line.tokens.front().kind == TK::EndKeyword;
  }
  EXPECT_EQ(begin_count, 3U);
  EXPECT_EQ(end_count, 3U);
}

TEST_F(TreeUnwrapperTest, MissingConditionalDelimitersRecoverAtOuterBlock) {
  for (const auto source : {
           "module m; initial begin if x = 1; end logic y; endmodule",
           "module m; initial begin case x 1: y = 1; endcase end "
           "logic z; endmodule",
       }) {
    const auto result = parseWithDiagnostics(source);
    EXPECT_TRUE(std::any_of(result.warnings.begin(), result.warnings.end(),
                            [](const auto& warning) {
                              return warning.code == "annex-a-fallback";
                            }));
    EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
              TK::EndModuleKeyword);
  }
}

TEST_F(TreeUnwrapperTest, ForHeadersUseProceduralOrGenerateProduction) {
  const auto procedural =
      parseWithDiagnostics("module m; initial for (;;) x = 1; endmodule");
  EXPECT_TRUE(procedural.warnings.empty());

  const auto generate = parseWithDiagnostics(
      "module m; generate for (; g < 2; g++) begin : item "
      "wire x; end endgenerate endmodule");
  EXPECT_TRUE(std::any_of(
      generate.warnings.begin(), generate.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
  EXPECT_FALSE(std::any_of(generate.warnings.begin(), generate.warnings.end(),
                           [](const auto& warning) {
                             return warning.code ==
                                    "token-conservation-fallback";
                           }));
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

TEST_F(TreeUnwrapperTest, LoopAlternativesCallAnnexBodyRules) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin forever x++; repeat (2) x++; "
      "while (x < 3) x++; for (int i = 0; i < 2; i++) x++; "
      "end generate for (genvar g = 0; g < 2; g++) "
      "begin : item wire y; end endgenerate endmodule");
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, ConditionalForeachIndicesResumeAnnexLoop) {
  const auto result = parseWithDiagnostics(
      "module m; initial foreach (a[\n"
      "`ifdef A\ni\n`else\nj\n`endif\n"
      "]) a[i] = 0; endmodule");
  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, MalformedForeachHeaderRecoversAtOuterEnd) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin foreach (a[i + 1]) x = 0; "
      "end endmodule");
  EXPECT_TRUE(std::any_of(
      result.lines.begin(), result.lines.end(), [](const auto& line) {
        return !line.tokens.empty() &&
               line.tokens.front().kind == TK::ForeachKeyword;
      }));
  EXPECT_TRUE(std::any_of(
      result.warnings.begin(), result.warnings.end(),
      [](const auto& warning) { return warning.code == "annex-a-fallback"; }));
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndKeyword);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
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

TEST_F(TreeUnwrapperTest, CaseItemListsCallExpressionRules) {
  const auto result = parseWithDiagnostics(
      "module m; initial case (x) 1, 2: y = 1; endcase "
      "generate case (1) 1, 2: begin : g wire z; end endcase "
      "endgenerate endmodule");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, CasePatternAndInsideItemsCallChildRules) {
  const auto result = parseWithDiagnostics(
      "module m; initial begin "
      "case (x) matches 1 &&& enabled: y = 1; endcase "
      "case (x) inside [1:$]: y = 2; endcase "
      "end endmodule");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, CaseXInsideFallsBackAndResumesAtModuleClose) {
  const auto result = parseWithDiagnostics(
      "module m; initial casex (a) inside "
      "1: b = 1; endcase endmodule module after; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  expectTokenConservation(result.lines);
  bool found_after = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() >= 2 &&
        line.tokens.front().kind == TK::ModuleKeyword &&
        line.tokens.at(1).rawText() == "after") {
      found_after = true;
    }
  }
  EXPECT_TRUE(found_after);
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
        line.tokens.at(1).rawText() == "c" &&
        line.tokens.back().kind == TK::Semicolon) {
      resumed = true;
    }
  }
  EXPECT_TRUE(resumed);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndModuleKeyword);
}

TEST_F(TreeUnwrapperTest, AnnexAConstructFamiliesKeepTokenOrder) {
  // Adjacent literals keep each SystemVerilog sample readable.
  // NOLINTBEGIN(bugprone-suspicious-missing-comma)
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
  // NOLINTEND(bugprone-suspicious-missing-comma)
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
    if (line.tokens.empty()) {
      continue;
    }
    if (line.tokens.front().rawText() == "a") {
      found_label = line.tokens.size() == kCaseLabelTokens &&
                    line.tokens.back().kind == TK::Colon;
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
  for (size_t i = 0; i < kManyModuleItems; ++i) {
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
  for (size_t i = 0; i < kLongBodyItems; ++i) {
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
  for (size_t i = 0; i < kLongBodyItems; ++i) {
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
  for (size_t i = 0; i < kLongBodyItems; ++i) {
    source += "int a" + std::to_string(i) + ";\n";
  }
  source += "endclass\nmodule m; function int f();\n";
  for (size_t i = 0; i < kLongBodyItems; ++i) {
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
  const auto result = parseWithDiagnostics(
      "package p; timeunit 1ns / 1ps; timeprecision 1ps; "
      "int a; endpackage");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
  EXPECT_EQ(result.lines.at(result.lines.size() - 2).tokens.front().kind,
            TK::EndPackageKeyword);
  const auto reverse = parseWithDiagnostics(
      "package p; timeprecision 1ps; timeunit 1ns; endpackage");
  ASSERT_TRUE(reverse.warnings.empty()) << reverse.warnings.front().message;
  expectTokenConservation(reverse.lines);
}

TEST_F(TreeUnwrapperTest, PackageHeaderCallsLifetimeAndIdentifierRules) {
  const auto result = parseWithDiagnostics(
      "package automatic p; int x; endpackage : p "
      "module after; endmodule");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, PackageHeaderResumesAfterConditionalLifetime) {
  const auto result = parseWithDiagnostics(
      "package\n"
      "`ifdef AUTOMATIC\n"
      "automatic\n"
      "`else\n"
      "static\n"
      "`endif\n"
      "p; int x; endpackage");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, AnonymousProgramCallsBodyItemRules) {
  const auto result = parseWithDiagnostics(
      "program; function int f(); return 1; endfunction "
      "endprogram module after; endmodule");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, ForkBlockUsesAnnexOpeningAndClosingLabels) {
  const auto result = parseWithDiagnostics(
      "module m; initial fork : workers a = 1; "
      "join_none : workers endmodule");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, IfConditionCallsCondPredicateRule) {
  const auto result = parseWithDiagnostics(
      "module m; initial if (a &&& b) x = 1; "
      "else if (c) x = 2; else x = 3; endmodule");
  ASSERT_TRUE(result.warnings.empty()) << result.warnings.front().message;
  expectTokenConservation(result.lines);
}

TEST_F(TreeUnwrapperTest, MalformedPackageHeaderResumesAfterEndpackage) {
  const auto result = parseWithDiagnostics(
      "package automatic; int x; endpackage module after; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  expectTokenConservation(result.lines);
  bool found_after = false;
  for (const auto& line : result.lines) {
    if (line.tokens.size() >= 2 &&
        line.tokens.front().kind == TK::ModuleKeyword &&
        line.tokens.at(1).rawText() == "after") {
      found_after = true;
    }
  }
  EXPECT_TRUE(found_after);
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
  EXPECT_EQ(result.lines.at(result.lines.size() - 3).tokens.front().kind,
            TK::EndFunctionKeyword);
}

TEST_F(TreeUnwrapperTest, GenerateLabelsStayWithTheirBlockKeywords) {
  const auto result = parseWithDiagnostics(
      "module m; generate if (1) begin : g logic a; end : g "
      "else begin : h logic b; end : h endgenerate endmodule");
  for (const auto& label : {"g", "h"}) {
    bool found = false;
    for (const auto& line : result.lines) {
      if (line.tokens.size() >= 3 &&
          line.tokens.at(0).kind == TK::BeginKeyword &&
          line.tokens.at(1).kind == TK::Colon &&
          line.tokens.at(2).rawText() == label) {
        found = true;
      }
    }
    EXPECT_TRUE(found) << label;
  }
  EXPECT_TRUE(result.warnings.empty());
}

TEST_F(TreeUnwrapperTest, GrammarTimingControlKeepsSimpleAlwaysLine) {
  for (const auto source : {
           "module m; always #5 clk = ~clk; endmodule",
           "module m; always #(1 + 2) clk = ~clk; endmodule",
       }) {
    const auto result = parseWithDiagnostics(source);
    ASSERT_GE(result.lines.size(), 3U);
    EXPECT_EQ(result.lines.at(1).tokens.front().kind, TK::AlwaysKeyword);
    EXPECT_EQ(result.lines.at(1).tokens.back().kind, TK::Semicolon);
    EXPECT_TRUE(result.warnings.empty()) << source;
  }
  const auto event =
      parseWithDiagnostics("module m; always @* clk = ~clk; endmodule");
  EXPECT_TRUE(event.warnings.empty());
  ASSERT_GE(event.lines.size(), 4U);
  EXPECT_EQ(event.lines.at(1).tokens.front().kind, TK::AlwaysKeyword);
  EXPECT_EQ(event.lines.at(2).tokens.back().kind, TK::Semicolon);
}

TEST_F(TreeUnwrapperTest, ConditionalEventControlResumesAnnexRule) {
  const auto result = parseWithDiagnostics(
      "module m; always @(\n"
      "`ifdef A\n"
      "posedge a\n"
      "`else\n"
      "posedge b\n"
      "`endif\n"
      ") begin end endmodule");
  EXPECT_TRUE(result.warnings.empty());
  bool saw_close = false;
  bool saw_begin = false;
  for (const auto& line : result.lines) {
    if (!line.tokens.empty() &&
        line.tokens.back().kind == TK::CloseParenthesis) {
      saw_close = true;
    }
    if (!line.tokens.empty() && line.tokens.front().kind == TK::BeginKeyword) {
      saw_begin = saw_close;
    }
  }
  EXPECT_TRUE(saw_begin);
}

TEST_F(TreeUnwrapperTest, MalformedEventControlRecoversAtOuterClose) {
  const auto result = parseWithDiagnostics(
      "module m; always @( begin end logic x; endmodule "
      "module n; logic y; endmodule");
  ASSERT_FALSE(result.warnings.empty());
  EXPECT_EQ(result.warnings.front().code, "annex-a-fallback");
  size_t module_closes = 0;
  bool parsed_second_module = false;
  for (const auto& line : result.lines) {
    if (line.tokens.empty() || line.is_opaque) {
      continue;
    }
    if (line.tokens.front().kind == TK::EndModuleKeyword) {
      ++module_closes;
    }
    if (line.tokens.front().kind == TK::LogicKeyword &&
        line.tokens.size() >= 2 && line.tokens.at(1).rawText() == "y") {
      parsed_second_module = true;
    }
  }
  EXPECT_EQ(module_closes, 2U);
  EXPECT_TRUE(parsed_second_module);
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

TEST_F(TreeUnwrapperTest, RepeatEventControlUsesAnnexAndRecoversAtOuterClose) {
  const auto valid = parseWithDiagnostics(
      "module m; initial begin repeat (2) @(\n"
      "`ifdef A\n"
      "posedge a\n"
      "`else\n"
      "posedge b\n"
      "`endif\n"
      ") q = 1; end endmodule");
  EXPECT_TRUE(valid.warnings.empty());

  const auto malformed = parseWithDiagnostics(
      "module m; initial begin repeat (2) @( begin end logic x; "
      "end endmodule module n; logic y; endmodule");
  ASSERT_FALSE(malformed.warnings.empty());
  EXPECT_EQ(malformed.warnings.front().code, "annex-a-fallback");
  bool parsed_second_module = false;
  for (const auto& line : malformed.lines) {
    if (line.tokens.size() >= 2 && !line.is_opaque &&
        line.tokens.front().kind == TK::LogicKeyword &&
        line.tokens.at(1).rawText() == "y") {
      parsed_second_module = true;
    }
  }
  EXPECT_TRUE(parsed_second_module);
}

// NOLINTEND(misc-use-internal-linkage,bugprone-throwing-static-initialization,cert-err58-cpp,cppcoreguidelines-owning-memory,modernize-use-trailing-return-type)
