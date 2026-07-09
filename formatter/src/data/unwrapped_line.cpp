
#include "data/unwrapped_line.h"

#include <ostream>
#include <string>
#include <string_view>

namespace format {

namespace {

using Token = slang::parsing::Token;
using Line = UnwrappedLine<Token>;
using PP = PartitionPolicy;

[[nodiscard]] auto policyName(PP policy) -> std::string_view {
  switch (policy) {
    case PP::kAlwaysExpand:
      return "AlwaysExpand";
    case PP::kFitOnLineElseExpand:
      return "FitOnLineElseExpand";
    case PP::kTabularAlignment:
      return "TabularAlignment";
    case PP::kAlreadyFormatted:
      return "AlreadyFormatted";
    case PP::kAssignmentAlignment:
      return "AssignmentAlignment";
  }
  return "Unknown";
}

[[nodiscard]] auto indent(size_t depth) -> std::string {
  std::string spaces;
  spaces.resize(depth * 2, ' ');
  return spaces;
}

auto printToken(const Token& token, size_t depth, size_t index,
                std::ostream& os) -> void {
  os << indent(depth) << "[" << index << "] "
     << slang::parsing::toString(token.kind) << " " << token.rawText() << "\n";
}

auto printLine(const Line& line, size_t depth, std::string_view label,
               std::ostream& os) -> void {
  os << indent(depth) << label << " indent=" << line.indentation_spaces
     << " policy=" << policyName(line.partition_policy)
     << " tokens=" << line.tokens.size() << "\n";

  size_t tokenIndex = 0;
  for (const auto& token : line.tokens) {
    printToken(token, depth + 1, tokenIndex, os);
    ++tokenIndex;
  }
}

// NOLINTEND(misc-no-recursion)

}  // namespace

auto printUnwrappedLine(const UnwrappedLine<slang::parsing::Token>& line,
                        size_t depth, std::ostream& os) -> void {
  printLine(line, depth, "line", os);
}

auto printUnwrappedLines(
    const std::vector<UnwrappedLine<slang::parsing::Token>>& lines,
    std::ostream& os) -> void {
  os << "UnwrappedLines count=" << lines.size() << "\n";
  size_t lineIndex = 0;
  for (const auto& line : lines) {
    const std::string label = "line " + std::to_string(lineIndex);
    printLine(line, 0, label, os);
    ++lineIndex;
  }
}

}  // namespace format
