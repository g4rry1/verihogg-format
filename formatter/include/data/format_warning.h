#pragma once

#include <slang/text/SourceLocation.h>

#include <string>

namespace format {

struct FormatWarning {
  slang::SourceLocation location;
  std::string code;
  std::string message;
};

}  // namespace format
