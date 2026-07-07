#include "pipeline/line_joiner.h"

#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

#include <cassert>
#include <vector>

#include "data/format_style.h"
#include "data/format_token.h"
#include "data/unwrapped_line.h"
#include "pipeline/compiler_directives.h"

namespace format {

namespace {

using TK = slang::parsing::TokenKind;
using TriviaKind = slang::parsing::TriviaKind;

[[nodiscard]] auto internalWidth(const UnwrappedLine<FormatToken>& line)
    -> size_t {
  size_t w = 0;
  for (size_t i = 0; i < line.tokens.size(); ++i) {
    if (i > 0) {
      w += line.tokens.at(i).before.spaces_required;
    }
    w += line.tokens.at(i).token.rawText().size();
  }
  return w;
}

[[nodiscard]] auto lineWidth(const UnwrappedLine<FormatToken>& line) -> size_t {
  return line.indentation_spaces + internalWidth(line);
}

[[nodiscard]] auto isCaseLabel(const UnwrappedLine<FormatToken>& line) -> bool {
  return !line.tokens.empty() && line.tokens.back().token.kind == TK::Colon &&
         line.partition_policy == PartitionPolicy::kTabularAlignment;
}

[[nodiscard]] auto startsWithCompilerDirective(
    const UnwrappedLine<FormatToken>& line) -> bool {
  return !line.tokens.empty() && isCompilerDirective(line.tokens.front().token);
}

[[nodiscard]] auto isJoinable(const UnwrappedLine<FormatToken>& line) -> bool {
  if (line.tokens.empty()) {
    return false;
  }
  if (startsWithCompilerDirective(line)) {
    return false;
  }
  if (line.partition_policy == PartitionPolicy::kAlreadyFormatted) {
    return false;
  }
  if (line.partition_policy == PartitionPolicy::kTabularAlignment &&
      !isCaseLabel(line)) {
    return false;
  }
  const TK first = line.tokens.front().token.kind;
  return first != TK::BeginKeyword && first != TK::ForkKeyword;
}

[[nodiscard]] auto isSimpleStatement(const UnwrappedLine<FormatToken>& line)
    -> bool {
  return !line.tokens.empty() && line.tokens.back().token.kind == TK::Semicolon;
}

[[nodiscard]] auto hasLeadingComment(const UnwrappedLine<FormatToken>& line)
    -> bool {
  if (line.tokens.empty()) {
    return false;
  }
  for (const auto& trivia : line.tokens.front().token.trivia()) {
    if (trivia.kind == TriviaKind::LineComment ||
        trivia.kind == TriviaKind::BlockComment) {
      return true;
    }
  }
  return false;
}

[[nodiscard]] auto endsWithOpenBlock(const UnwrappedLine<FormatToken>& line)
    -> bool {
  if (line.tokens.empty()) {
    return false;
  }

  const TK last = line.tokens.back().token.kind;
  return last == TK::BeginKeyword || last == TK::ForkKeyword;
}

auto absorb(UnwrappedLine<FormatToken>& anchor,
            UnwrappedLine<FormatToken>& next) -> void {
  assert(!next.tokens.empty());
  next.tokens.front().before.spaces_required = 1;
  next.tokens.front().before.break_decision = BreakDecision::kMustNotBreak;
  anchor.tokens.insert(anchor.tokens.end(),
                       std::make_move_iterator(next.tokens.begin()),
                       std::make_move_iterator(next.tokens.end()));
}

}  // namespace

auto LineJoiner::join(std::vector<UnwrappedLine<FormatToken>>& lines) const
    -> void {
  if (lines.size() < 2) {
    return;
  }

  const FormatStyle& st = style.get();
  std::vector<UnwrappedLine<FormatToken>> result;
  result.reserve(lines.size());

  size_t i = 0;
  while (i < lines.size()) {
    UnwrappedLine<FormatToken> anchor = std::move(lines.at(i));
    const size_t anchor_indent = anchor.indentation_spaces;
    ++i;

    if (isJoinable(anchor) && !endsWithOpenBlock(anchor)) {
      while (i < lines.size()) {
        const size_t next_indent = lines.at(i).indentation_spaces;

        if (next_indent > anchor_indent) {
          if (hasLeadingComment(lines.at(i))) {
            break;
          }
          if (isSimpleStatement(lines.at(i)) && isJoinable(lines.at(i))) {
            if (lineWidth(anchor) + 1 + internalWidth(lines.at(i)) >
                st.column_limit) {
              break;
            }
            absorb(anchor, lines.at(i++));
            continue;
          }

          break;
        }

        if (next_indent == anchor_indent && !lines.at(i).tokens.empty() &&
            lines.at(i).tokens.front().type == TokenType::kElseKeyword &&
            !hasLeadingComment(lines.at(i))) {
          if (i + 1 >= lines.size()) {
            break;
          }
          if (lines.at(i + 1).indentation_spaces <= anchor_indent) {
            break;
          }
          if (hasLeadingComment(lines.at(i + 1))) {
            break;
          }

          if (isSimpleStatement(lines.at(i + 1)) &&
              isJoinable(lines.at(i + 1))) {
            const size_t w = lineWidth(anchor) + 1 +
                             internalWidth(lines.at(i)) + 1 +
                             internalWidth(lines.at(i + 1));
            if (w > st.column_limit) {
              break;
            }
            absorb(anchor, lines.at(i++));  // else [if (...)]
            absorb(anchor, lines.at(i++));  // body
            continue;
          }

          break;
        }

        break;
      }
    }

    result.push_back(std::move(anchor));
  }

  lines = std::move(result);
}

}  // namespace format
