#pragma once

#include <slang/ast/Compilation.h>
#include <slang/parsing/Token.h>

#include <gsl/span>

#include "data/format_style.h"
#include "data/format_warning.h"
#include "data/unwrapped_line.h"

namespace format {

struct UnwrapResult {
  std::vector<UnwrappedLine<slang::parsing::Token>> lines;
  std::vector<FormatWarning> warnings;
};

class TreeUnwrapper {
 public:
  TreeUnwrapper(gsl::span<const slang::parsing::Token> tokens,
                const FormatStyle& style)
      : tokens(tokens), style(style) {}

  [[nodiscard]] auto unwrap() const
      -> std::vector<UnwrappedLine<slang::parsing::Token>>;
  [[nodiscard]] auto unwrapWithDiagnostics() const -> UnwrapResult;

 private:
  gsl::span<const slang::parsing::Token> tokens;
  std::reference_wrapper<const FormatStyle> style;
};
}  // namespace format
