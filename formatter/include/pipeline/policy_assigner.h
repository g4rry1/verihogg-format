#pragma once

#include <functional>
#include <vector>

#include "data/format_style.h"
#include "data/format_token.h"
#include "data/unwrapped_line.h"

namespace format {

class PolicyAssigner {
 public:
  using Line = UnwrappedLine<FormatToken>;

  explicit PolicyAssigner(const FormatStyle& style) : style_(style) {}

  auto assign(std::vector<Line>& lines) const -> void;

 private:
  std::reference_wrapper<const FormatStyle> style_;
};

}  // namespace format
