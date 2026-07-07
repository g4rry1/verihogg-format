#pragma once

#include <slang/parsing/Token.h>
#include <slang/util/BumpAllocator.h>

#include <gsl/span>
#include <vector>

namespace format {

[[nodiscard]] auto normalizeTokens(
    gsl::span<const slang::parsing::Token> tokens,
    slang::BumpAllocator& allocator) -> std::vector<slang::parsing::Token>;

}  // namespace format
