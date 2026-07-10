#include "pipeline/tabular_aligner.h"

#include <algorithm>
#include <cstddef>
#include <string_view>

namespace format {

static constexpr size_t kMinColumnGap = 4;
static constexpr size_t kMinGroupSize = 2;
static constexpr size_t kCommentColumnGap = 8;
static constexpr size_t kMinSpacesBeforeAssignment = 2;
static constexpr size_t kMinSpacesAfterAssignment = 1;
static constexpr size_t kMinSpacesCaseItem = 1;
static constexpr size_t kMinSpacesPortDirectionType = 2;
static constexpr size_t kMinSpacesPortTypeName = 8;

struct AlignmentCell {
  size_t start_idx = 0;
  size_t end_idx = 0;
  size_t width = 0;
};

using AlignmentRow = std::vector<AlignmentCell>;

struct AlignmentGroup {
  PartitionPolicy policy = PartitionPolicy::kAlwaysExpand;
  std::vector<size_t> line_indices;
  size_t num_columns = 0;
  std::vector<AlignmentRow> table;
  std::vector<size_t> col_max_width;
};

[[nodiscard]] static auto is_assignment_operator(const FormatToken& ft)
    -> bool {
  using TK = slang::parsing::TokenKind;
  return ft.type == TokenType::kAssignmentOperator ||
         ft.token.kind == TK::LessThanEquals;
}

[[nodiscard]] static auto is_directive_line(
    const UnwrappedLine<FormatToken>& line) -> bool {
  if (line.tokens.empty()) {
    return false;
  }
  return line.tokens.front().token.kind == slang::parsing::TokenKind::Directive;
}

[[nodiscard]] auto static range_width(const std::vector<FormatToken>& tokens,
                                      size_t start, size_t end) -> size_t {
  size_t width = 0;
  for (size_t i = start; i < end; ++i) {
    if (i != start) {
      width += tokens.at(i).before.spaces_required;
    }
    width += tokens.at(i).token.rawText().size();
  }
  return width;
}

[[nodiscard]] static auto is_suffix_token(const FormatToken& ft) -> bool {
  if (ft.type != TokenType::kUnknown) {
    return ft.type == TokenType::kComma || ft.type == TokenType::kSemicolon;
  }
  using TK = slang::parsing::TokenKind;
  return ft.token.kind == TK::Comma || ft.token.kind == TK::Semicolon;
}

[[nodiscard]] auto static build_row(const UnwrappedLine<FormatToken>& line)
    -> AlignmentRow {
  AlignmentRow row;
  const auto& tokens = line.tokens;
  if (tokens.empty()) {
    return row;
  }

  size_t cell_start = 0;

  auto close_cell = [&](size_t end) {
    if (end <= cell_start) {
      return;
    }
    row.push_back(AlignmentCell{
        .start_idx = cell_start,
        .end_idx = end,
        .width = range_width(tokens, cell_start, end),
    });
    cell_start = end;
  };

  size_t i = 0;
  while (i < tokens.size()) {
    const FormatToken& ft = tokens.at(i);
    if (ft.balancing == GroupBalancing::kOpen) {
      if (ft.matching_bracket != nullptr) {
        size_t j = i + 1;
        while (j < tokens.size() && &tokens.at(j) != ft.matching_bracket) {
          ++j;
        }
        i = j + 1;
      } else {
        size_t depth = 1;
        ++i;
        while (i < tokens.size() && depth > 0) {
          if (tokens.at(i).balancing == GroupBalancing::kOpen) {
            ++depth;
          }
          if (tokens.at(i).balancing == GroupBalancing::kClose) {
            --depth;
          }
          ++i;
        }
      }
      continue;
    }
    if (is_suffix_token(ft) || (i > 0 && ft.before.spaces_required == 0)) {
      ++i;
      continue;
    }
    close_cell(i);
    ++i;
  }
  close_cell(tokens.size());
  return row;
}

[[nodiscard]] static auto build_assignment_row(UnwrappedLine<FormatToken>& line)
    -> AlignmentRow {
  AlignmentRow row;
  auto& tokens = line.tokens;
  if (tokens.empty()) {
    return row;
  }

  size_t op_idx = tokens.size();
  int depth = 0;

  for (size_t i = 0; i < tokens.size(); ++i) {
    const auto& ft = tokens.at(i);

    if (ft.balancing == GroupBalancing::kOpen) {
      ++depth;
      continue;
    }
    if (ft.balancing == GroupBalancing::kClose) {
      --depth;
      continue;
    }
    if (depth > 0) {
      continue;
    }

    if (is_assignment_operator(ft)) {
      op_idx = i;
      break;
    }
  }

  if (op_idx == tokens.size()) {
    return row;
  }

  AlignmentCell left_cell{.start_idx = 0,
                          .end_idx = op_idx,
                          .width = range_width(tokens, 0, op_idx)};

  AlignmentCell right_cell{.start_idx = op_idx,
                           .end_idx = tokens.size(),
                           .width = range_width(tokens, op_idx, tokens.size())};

  row.push_back(left_cell);
  row.push_back(right_cell);
  return row;
}

[[nodiscard]] static auto has_comment(
    const std::vector<UnwrappedLine<FormatToken>>& lines, size_t line_idx)
    -> bool {
  const size_t next_idx = line_idx + 1;
  if (next_idx >= lines.size()) {
    return false;
  }

  const auto& next_tokens = lines.at(next_idx).tokens;
  if (next_tokens.empty()) {
    return false;
  }

  for (const auto& trivia : next_tokens.at(0).token.trivia()) {
    using TK = slang::parsing::TriviaKind;
    if (trivia.kind == TK::LineComment || trivia.kind == TK::BlockComment) {
      return true;
    }
    if (trivia.kind == TK::EndOfLine) {
      break;
    }
  }
  return false;
}

[[nodiscard]] static auto is_case_item_group(
    const AlignmentGroup& group,
    const std::vector<UnwrappedLine<FormatToken>>& lines) -> bool {
  if (group.policy != PartitionPolicy::kTabularAlignment ||
      group.num_columns < 2 || group.table.empty()) {
    return false;
  }
  const auto& tokens = lines.at(group.line_indices.front()).tokens;
  const AlignmentCell& second = group.table.front().at(1);
  return (second.end_idx > second.start_idx) &&
         tokens.at(second.start_idx).token.kind ==
             slang::parsing::TokenKind::Colon;
}

[[nodiscard]] static auto is_port_list_group(
    const AlignmentGroup& group,
    const std::vector<UnwrappedLine<FormatToken>>& lines) -> bool {
  if (group.policy != PartitionPolicy::kTabularAlignment ||
      group.line_indices.empty()) {
    return false;
  }
  const auto& tokens = lines.at(group.line_indices.front()).tokens;
  return !tokens.empty() && tokens.front().type == TokenType::kPortDirection;
}

[[nodiscard]] static auto gap_before_column(
    const AlignmentGroup& group,
    const std::vector<UnwrappedLine<FormatToken>>& lines, size_t column_index)
    -> size_t {
  if (group.policy == PartitionPolicy::kAssignmentAlignment) {
    return kMinSpacesBeforeAssignment;
  }
  if (is_case_item_group(group, lines)) {
    return kMinSpacesCaseItem;
  }
  if (is_port_list_group(group, lines)) {
    if (column_index == 1) {
      return kMinSpacesPortDirectionType;
    }
    if (column_index == 2) {
      return kMinSpacesPortTypeName;
    }
  }
  return kMinColumnGap;
}

static void apply_group(AlignmentGroup& group,
                        std::vector<UnwrappedLine<FormatToken>>& lines) {
  if (group.line_indices.size() < kMinGroupSize) {
    return;
  }

  std::vector<size_t> column_offset(group.num_columns, 0);
  for (size_t c = 1; c < group.num_columns; ++c) {
    const size_t gap = gap_before_column(group, lines, c);
    column_offset.at(c) =
        column_offset.at(c - 1) + group.col_max_width.at(c - 1) + gap;
  }

  const size_t formatted_code_width =
      column_offset.empty() ? 0
                            : column_offset.back() + group.col_max_width.back();

  size_t max_total_width = 0;
  for (size_t line_i : group.line_indices) {
    const size_t indent = lines.at(line_i).indentation_spaces;
    max_total_width = std::max(max_total_width, indent + formatted_code_width);
  }

  const size_t comment_column = max_total_width + kCommentColumnGap;
  bool any_comment = false;
  for (size_t line_i : group.line_indices) {
    if (has_comment(lines, line_i)) {
      any_comment = true;
      break;
    }
  }

  for (size_t row_i = 0; row_i < group.line_indices.size(); ++row_i) {
    const size_t line_i = group.line_indices.at(row_i);
    auto& line = lines.at(line_i);
    auto& tokens = line.tokens;
    const AlignmentRow& row = group.table.at(row_i);

    size_t cursor = line.indentation_spaces;

    for (size_t c = 0; c < row.size(); ++c) {
      const AlignmentCell& cell = row.at(c);

      if (c == 0) {
        cursor = line.indentation_spaces + cell.width;
        continue;
      }
      const size_t target_abs = line.indentation_spaces + column_offset.at(c);
      const size_t spaces = (target_abs > cursor) ? (target_abs - cursor) : 1;

      FormatToken& first = tokens.at(cell.start_idx);
      first.before.spaces_required = spaces;

      cursor = target_abs + cell.width;

      if (group.policy == PartitionPolicy::kAssignmentAlignment && c == 1) {
        if (cell.start_idx + 1 < tokens.size()) {
          tokens.at(cell.start_idx + 1).before.spaces_required =
              kMinSpacesAfterAssignment;
        }
      }
    }
    if (any_comment) {
      const size_t next_i = line_i + 1;
      if (next_i < lines.size() && !lines.at(next_i).tokens.empty()) {
        const size_t spaces = (comment_column > cursor)
                                  ? (comment_column - cursor)
                                  : kCommentColumnGap;

        lines.at(next_i).tokens.at(0).before.comment_spaces = spaces;
      }
    }
    line.partition_policy = PartitionPolicy::kAlreadyFormatted;
  }
}

static void process_lines(std::vector<UnwrappedLine<FormatToken>>& lines) {
  AlignmentGroup current_group;

  auto flush = [&]() {
    apply_group(current_group, lines);
    current_group = AlignmentGroup{};
  };

  for (size_t i = 0; i < lines.size(); ++i) {
    auto& line = lines.at(i);

    const bool is_tabular =
        (line.partition_policy == PartitionPolicy::kTabularAlignment);
    const bool is_assignment =
        (line.partition_policy == PartitionPolicy::kAssignmentAlignment);

    if (!is_tabular && !is_assignment) {
      if (is_directive_line(line)) {
        continue;
      }
      if (!current_group.line_indices.empty()) {
        flush();
      }
      continue;
    }

    if (line.tokens.empty()) {
      if (!current_group.line_indices.empty()) {
        flush();
      }
      continue;
    }

    AlignmentRow row;
    if (is_tabular) {
      row = build_row(line);
    } else {
      row = build_assignment_row(line);
    }

    if (row.empty()) {
      if (!current_group.line_indices.empty()) {
        flush();
      }
      continue;
    }

    const size_t ncols = row.size();

    if (!current_group.line_indices.empty() &&
        (current_group.num_columns != ncols ||
         current_group.policy != line.partition_policy)) {
      flush();
    }

    if (current_group.line_indices.empty()) {
      current_group.num_columns = ncols;
      current_group.col_max_width.assign(ncols, 0);
      current_group.policy = line.partition_policy;
    }

    for (size_t c = 0; c < ncols; ++c) {
      current_group.col_max_width.at(c) =
          std::max(current_group.col_max_width.at(c), row.at(c).width);
    }

    current_group.line_indices.push_back(i);
    current_group.table.push_back(std::move(row));
  }
  flush();
}

void align(std::vector<UnwrappedLine<FormatToken>>& lines,
           const FormatStyle& /*style*/) {
  process_lines(lines);
}

}  // namespace format
