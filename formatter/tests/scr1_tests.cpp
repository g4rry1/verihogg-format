#include <data/lex_context.h>
#include <gtest/gtest.h>
#include <slang/parsing/TokenKind.h>
#include <slang/syntax/SyntaxKind.h>
#include <slang/syntax/SyntaxNode.h>
#include <slang/syntax/SyntaxTree.h>
#include <slang/text/SourceManager.h>

#include <filesystem>
#include <fstream>
#include <string>
#include <string_view>

#include "formatter.h"

namespace {

[[nodiscard]] auto lowercaseAscii(char ch) -> char {
  if (ch >= 'A' && ch <= 'Z') {
    return static_cast<char>(ch - 'A' + 'a');
  }
  return ch;
}

[[nodiscard]] auto lowercaseAsciiText(std::string_view text) -> std::string {
  std::string normalized{text};
  for (char& ch : normalized) {
    ch = lowercaseAscii(ch);
  }
  return normalized;
}

[[nodiscard]] auto isNormalizedNumericTextEquivalent(
    slang::syntax::SyntaxKind parentKind, slang::parsing::TokenKind tokenKind,
    std::string_view left, std::string_view right) -> bool {
  using SK = slang::syntax::SyntaxKind;
  using TK = slang::parsing::TokenKind;

  switch (tokenKind) {
    case TK::IntegerBase:
    case TK::IntegerLiteral:
    case TK::UnbasedUnsizedLiteral:
    case TK::RealLiteral:
    case TK::TimeLiteral:
      return lowercaseAsciiText(left) == lowercaseAsciiText(right);

    case TK::Identifier:
      return parentKind == SK::IntegerVectorExpression &&
             lowercaseAsciiText(left) == lowercaseAsciiText(right);

    default:
      return false;
  }
}

void compareTrees(const slang::syntax::SyntaxNode& a,
                  const slang::syntax::SyntaxNode& b) {
  ASSERT_EQ(a.kind, b.kind)
      << "Node kind mismatch: " << slang::syntax::toString(a.kind) << " vs "
      << slang::syntax::toString(b.kind);
  ASSERT_EQ(a.getChildCount(), b.getChildCount())
      << "Child count mismatch in node " << slang::syntax::toString(a.kind);

  for (uint32_t i = 0; i < a.getChildCount(); i++) {
    auto aNode = a.childNode(i);
    auto bNode = b.childNode(i);

    if (aNode && bNode) {
      compareTrees(*aNode, *bNode);
    } else if (!aNode && !bNode) {
      auto aTok = a.childToken(i);
      auto bTok = b.childToken(i);
      EXPECT_EQ(aTok.kind, bTok.kind)
          << "Token kind mismatch at child " << i << " of "
          << slang::syntax::toString(a.kind) << ": '" << aTok.rawText()
          << "' vs '" << bTok.rawText() << "'";
      EXPECT_TRUE(
          aTok.rawText() == bTok.rawText() ||
          isNormalizedNumericTextEquivalent(a.kind, aTok.kind, aTok.rawText(),
                                            bTok.rawText()))
          << "Token text mismatch at child " << i << " of "
          << slang::syntax::toString(a.kind);
    } else {
      ADD_FAILURE() << "Child type mismatch at index " << i << " of node "
                    << slang::syntax::toString(a.kind)
                    << " (one is a node, other is a token)";
    }
  }
}

auto collectSvFiles() -> std::vector<std::string> {
  namespace fs = std::filesystem;
  if (std::string(SCR1_DIR).empty()) {
    return {};
  }
  std::vector<std::string> files;
  fs::path dir{SCR1_DIR "/src"};
  if (!fs::exists(dir)) {
    return {};
  }
  for (const auto& entry : fs::recursive_directory_iterator(dir)) {
    if (entry.path().extension() == ".sv" ||
        entry.path().extension() == ".svh") {
      files.push_back(entry.path().string());
    }
  }
  std::ranges::sort(files);
  return files;
}

}  // namespace

class Scr1IntegrationTest : public ::testing::TestWithParam<std::string> {
 private:
  slang::SourceManager sm;

 protected:
  void SetUp() override {
    ASSERT_FALSE(sm.addUserDirectories(SCR1_DIR "/src/includes"))
        << "Could not add scr1 include directory";
  }

  void assertFormatPreservesTree(const std::string& path) {
    std::ifstream f(path);
    ASSERT_TRUE(f.is_open()) << "Cannot open: " << path;
    std::string original{std::istreambuf_iterator<char>(f),
                         std::istreambuf_iterator<char>()};

    LexContext ctx;
    auto tokens = ctx.lex_string(original);
    ASSERT_FALSE(tokens.empty()) << "Failed to lex: " << path;

    auto result = format::format(tokens, format::FormatStyle{});

    // fromText for both so neither expands `include / macros — same pipeline
    auto origTree = slang::syntax::SyntaxTree::fromText(original, sm, path);
    auto fmtTree = slang::syntax::SyntaxTree::fromText(result.formatted_text,
                                                       sm, path + "_fmt");

    compareTrees(origTree->root(), fmtTree->root());
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Scr1IntegrationTest);

TEST_P(Scr1IntegrationTest, FormatPreservesTree) {
  assertFormatPreservesTree(GetParam());
}

INSTANTIATE_TEST_SUITE_P(AllSvFiles, Scr1IntegrationTest,
                         testing::ValuesIn(collectSvFiles()),
                         [](const testing::TestParamInfo<std::string>& info) {
                           auto p = std::filesystem::path(info.param);
                           return p.stem().string() + "_" +
                                  p.extension().string().substr(1);
                         });
