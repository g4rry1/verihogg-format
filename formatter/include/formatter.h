#pragma once

#include <slang/parsing/Token.h>

#include <gsl/span>
#include <string>
#include <vector>

#include "data/format_style.h"
#include "data/format_warning.h"

namespace format {
struct FormatResult {
  std::string formatted_text;
  std::vector<FormatWarning> warnings;
};

auto format(gsl::span<const slang::parsing::Token> tokens, FormatStyle style)
    -> FormatResult;
}  // namespace format
