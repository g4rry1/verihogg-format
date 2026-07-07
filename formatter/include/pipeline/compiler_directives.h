#pragma once

#include <slang/parsing/Token.h>
#include <slang/parsing/TokenKind.h>

#include <string_view>

namespace format {

[[nodiscard]] inline auto isCompilerDirective(slang::parsing::Token tok)
    -> bool {
  namespace parsing = slang::parsing;

  if (tok.kind != parsing::TokenKind::Directive) {
    return false;
  }

  const std::string_view text = tok.rawText();
  return text == "`begin_keywords" || text == "`celldefine" ||
         text == "`default_decay_time" || text == "`default_nettype" ||
         text == "`default_trireg_strength" || text == "`define" ||
         text == "`else" || text == "`elsif" || text == "`end_keywords" ||
         text == "`endcelldefine" || text == "`endif" ||
         text == "`endprotect" || text == "`endprotected" || text == "`ifdef" ||
         text == "`ifndef" || text == "`include" || text == "`line" ||
         text == "`nounconnected_drive" || text == "`pragma" ||
         text == "`protect" || text == "`protected" || text == "`resetall" ||
         text == "`timescale" || text == "`unconnected_drive" ||
         text == "`undef" || text == "`undefineall";
}

}  // namespace format
