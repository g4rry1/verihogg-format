#include "formatter.h"

#include <slang/parsing/Token.h>

#include <gsl/span>
#include <sstream>

#include "data/format_style.h"
#include "pipeline/line_joiner.h"
#include "pipeline/line_wrap_searcher.h"
#include "pipeline/policy_assigner.h"
#include "pipeline/printer.h"
#include "pipeline/tabular_aligner.h"
#include "pipeline/token_annotator.h"
#include "pipeline/token_normalizer.h"
#include "pipeline/tree_unwrapper.h"

namespace format {
auto format(gsl::span<const slang::parsing::Token> tokens, FormatStyle style)
    -> FormatResult {
  slang::BumpAllocator normalizer_allocator;
  auto normalizedTokens = normalizeTokens(tokens, normalizer_allocator);
  auto unwrapResult =
      TreeUnwrapper(normalizedTokens, style).unwrapWithDiagnostics();
  auto annotatedLines = TokenAnnotator(style).annotate(unwrapResult.lines);
  PolicyAssigner(style).assign(annotatedLines);
  LineJoiner(style).join(annotatedLines);
  align(annotatedLines, style);
  applyLineWraps(annotatedLines, style);
  std::ostringstream oss;
  Printer(style).print(annotatedLines, oss);
  return FormatResult{.formatted_text = oss.str(),
                      .warnings = std::move(unwrapResult.warnings)};
}
}  // namespace format
