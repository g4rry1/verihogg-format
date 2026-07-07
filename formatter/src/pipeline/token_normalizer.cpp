#include "pipeline/token_normalizer.h"

#include <slang/parsing/TokenKind.h>

#include <cstddef>
#include <cstring>
#include <string>
#include <string_view>

namespace format {
namespace {

using TK = slang::parsing::TokenKind;
using slang::parsing::Token;

[[nodiscard]] auto lowercaseAscii(char ch) -> char {
  if (ch >= 'A' && ch <= 'Z') {
    return static_cast<char>(ch - 'A' + 'a');
  }
  return ch;
}

[[nodiscard]] auto lowercaseAsciiText(std::string_view text) -> std::string {
  std::string normalized{text};
  for (char& ch : normalized) {
    ch = lowercaseAscii(ch);
  }
  return normalized;
}

[[nodiscard]] auto isDigit(char ch) -> bool { return ch >= '0' && ch <= '9'; }

[[nodiscard]] auto isExponentMarker(std::string_view text, size_t index)
    -> bool {
  if (index == 0 || index + 1 >= text.size()) {
    return false;
  }

  size_t next = index + 1;
  if (text.at(next) == '+' || text.at(next) == '-') {
    ++next;
  }
  return next < text.size() && isDigit(text.at(next));
}

[[nodiscard]] auto normalizeRealText(std::string_view text) -> std::string {
  std::string normalized{text};
  for (size_t i = 0; i < normalized.size(); ++i) {
    if (normalized.at(i) == 'E' && isExponentMarker(normalized, i)) {
      normalized.at(i) = 'e';
    }
  }
  return normalized;
}

[[nodiscard]] auto normalizedRawText(const Token& token,
                                     bool after_integer_base) -> std::string {
  switch (token.kind) {
    case TK::Identifier:
      if (after_integer_base) {
        return lowercaseAsciiText(token.rawText());
      }
      return std::string{token.rawText()};

    case TK::IntegerBase:
    case TK::IntegerLiteral:
    case TK::UnbasedUnsizedLiteral:
      return lowercaseAsciiText(token.rawText());

    case TK::RealLiteral:
    case TK::TimeLiteral:
      return normalizeRealText(token.rawText());

    default:
      return std::string{token.rawText()};
  }
}

[[nodiscard]] auto copyRawText(std::string_view text,
                               slang::BumpAllocator& allocator)
    -> std::string_view {
  auto copied = allocator.copyFrom(std::span{text.data(), text.size()});
  return {copied.data(), copied.size()};
}

}  // namespace

[[nodiscard]] auto normalizeTokens(gsl::span<const Token> tokens,
                                   slang::BumpAllocator& allocator)
    -> std::vector<Token> {
  std::vector<Token> normalized;
  normalized.reserve(tokens.size());

  bool after_integer_base = false;
  for (const Token& token : tokens) {
    const std::string raw_text = normalizedRawText(token, after_integer_base);
    after_integer_base = token.kind == TK::IntegerBase;

    if (raw_text == token.rawText()) {
      normalized.push_back(token);
      continue;
    }

    normalized.push_back(
        token.withRawText(allocator, copyRawText(raw_text, allocator)));
  }

  return normalized;
}

}  // namespace format
