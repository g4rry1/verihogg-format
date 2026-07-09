#pragma once

#include <slang/syntax/SyntaxNode.h>

#include <concepts>
#include <cstdint>
#include <iostream>
#include <vector>

#include "format_style.h"

namespace format {

enum class PartitionPolicy : uint8_t {
  kAlwaysExpand,
  kFitOnLineElseExpand,
  kTabularAlignment,
  kAlreadyFormatted,
  kAssignmentAlignment,
};

template <typename Token>
struct UnwrappedLine {
  std::vector<Token> tokens;

  IndentLevel indentation_spaces = 0;
  PartitionPolicy partition_policy = PartitionPolicy::kAlwaysExpand;

  auto map(std::invocable<Token&&> auto&& func) && -> UnwrappedLine<
      std::invoke_result_t<decltype(func), Token&&>> {
    using T = std::invoke_result_t<decltype(func), Token&&>;
    std::vector<T> tokens{};
    std::transform(
        std::make_move_iterator(this->tokens.begin()),
        std::make_move_iterator(this->tokens.end()), std::back_inserter(tokens),
        [&func](Token&& token) -> auto {
          return std::forward<decltype(func)>(func)(std::move(token));
        });
    return {
        .tokens = std::move(tokens),
        .indentation_spaces = this->indentation_spaces,
        .partition_policy = this->partition_policy,
    };
  }

  auto map(std::invocable<const Token&> auto&& func) const
      -> UnwrappedLine<std::invoke_result_t<decltype(func), const Token&>> {
    using T = std::invoke_result_t<decltype(func), const Token&>;
    std::vector<T> tokens{};
    std::transform(this->tokens.begin(), this->tokens.end(),
                   std::back_inserter(tokens),
                   [&func](const Token& token) -> auto {
                     return std::forward<decltype(func)>(func)(token);
                   });
    return {
        .tokens = std::move(tokens),
        .indentation_spaces = this->indentation_spaces,
        .partition_policy = this->partition_policy,
    };
  }
};

auto printUnwrappedLine(const UnwrappedLine<slang::parsing::Token>& line,
                        size_t depth = 0, std::ostream& os = std::cout) -> void;

// Prints debug representation: includes token kinds, indices, and indentation
// metadata — not the formatted source text.
auto printUnwrappedLines(
    const std::vector<UnwrappedLine<slang::parsing::Token>>& lines,
    std::ostream& os = std::cout) -> void;

}  // namespace format
