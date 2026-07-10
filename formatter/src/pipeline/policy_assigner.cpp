#include "pipeline/policy_assigner.h"

#include <slang/parsing/TokenKind.h>

namespace format {

namespace {

using TK = slang::parsing::TokenKind;
using Line = PolicyAssigner::Line;

[[nodiscard]] auto isBlockHeader(const Line& line) -> bool {
  if (line.tokens.empty()) {
    return false;
  }
  switch (line.tokens.front().token.kind) {
    case TK::ModuleKeyword:
    case TK::MacromoduleKeyword:
    case TK::InterfaceKeyword:
    case TK::PackageKeyword:
    case TK::ProgramKeyword:
    case TK::ClassKeyword:
    case TK::FunctionKeyword:
    case TK::TaskKeyword:
      return true;
    default:
      return false;
  }
}

[[nodiscard]] auto isPortListOpen(const Line& line) -> bool {
  return line.tokens.size() == 1 &&
         line.tokens.front().token.kind == TK::OpenParenthesis;
}

[[nodiscard]] auto isCaseItemLabel(const Line& line) -> bool {
  if (line.tokens.empty() || line.tokens.back().token.kind != TK::Colon) {
    return false;
  }
  for (const auto& ft : line.tokens) {
    if (ft.type == TokenType::kAssignmentOperator) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] auto isDeclarationLine(const Line& line) -> bool {
  if (line.tokens.empty()) {
    return false;
  }
  if (line.tokens.back().token.kind != TK::Semicolon) {
    return false;
  }
  for (const auto& ft : line.tokens) {
    if (ft.nesting_level == 0 && ft.token.kind == TK::OpenParenthesis) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] auto requiresTabularAlignment(const Line& line) -> bool {
  for (const auto& ft : line.tokens) {
    if (ft.type == TokenType::kPortDirection ||
        ft.type == TokenType::kTypeKeyword) {
      return true;
    }
  }
  bool hasTypeName = false;
  for (const auto& ft : line.tokens) {
    if (ft.type == TokenType::kTypeName) {
      hasTypeName = true;
      break;
    }
  }
  if (hasTypeName && isDeclarationLine(line)) {
    return true;
  }

  return false;
}

[[nodiscard]] auto requiresAssignmentAlignment(const Line& line) -> bool {
  bool hasAssignment = false;
  bool hasControlKeyword = false;

  for (const auto& ft : line.tokens) {
    if (ft.nesting_level > 0) {
      continue;
    }
    if (ft.type == TokenType::kAssignmentOperator ||
        ft.token.kind == TK::LessThanEquals) {
      hasAssignment = true;
      continue;
    }
    if (ft.token.kind == TK::IfKeyword || ft.token.kind == TK::CaseKeyword ||
        ft.token.kind == TK::ForKeyword || ft.token.kind == TK::WhileKeyword ||
        ft.token.kind == TK::ForeachKeyword ||
        ft.token.kind == TK::RepeatKeyword ||
        ft.token.kind == TK::ForeverKeyword || ft.token.kind == TK::DoKeyword) {
      hasControlKeyword = true;
    }
  }

  return hasAssignment && !hasControlKeyword;
}

}  // namespace

auto PolicyAssigner::assign(std::vector<Line>& lines) const -> void {
  for (auto& line : lines) {
    if (isBlockHeader(line) || isPortListOpen(line)) {
      line.partition_policy = PartitionPolicy::kFitOnLineElseExpand;
    } else if (requiresAssignmentAlignment(line)) {
      line.partition_policy = PartitionPolicy::kAssignmentAlignment;
    } else if (isCaseItemLabel(line) || requiresTabularAlignment(line)) {
      line.partition_policy = PartitionPolicy::kTabularAlignment;
    } else {
      line.partition_policy = PartitionPolicy::kAlwaysExpand;
    }
  }
}

}  // namespace format
