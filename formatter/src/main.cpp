#include <slang/driver/Driver.h>

#include <cassert>
#include <exception>
#include <iostream>
#include <string_view>

#include "cli/format_args.h"
#include "data/lex_context.h"
#include "formatter.h"
#include "pipeline/runner.h"

namespace {

auto printWarning(std::ostream& os, std::string_view path,
                  const format::FormatWarning& warning) -> void {
  os << "Warning";
  if (!path.empty()) {
    os << " in " << path;
  }
  os << ": " << warning.message << " [" << warning.code << "]\n";
}

}  // namespace

auto main(int argc, char** argv) -> int {
  try {
    slang::driver::Driver driver;
    driver.addStandardArgs();

    format::FormatArgsBinder binder(driver);
    auto args = gsl::span(argv, argc);
    for (std::string_view arg : args.subspan(1)) {
      if (arg == "--help" || arg == "-h") {
        binder.printFormatterHelp();
        return 0;
      }
    }

    if (!driver.parseCommandLine(argc, argv)) {
      return 1;
    }

    auto [style, run] = binder.buildStyle();

    const auto& files = driver.sourceLoader.getFilePaths();

    if (run.inplace && files.empty()) {
      std::cerr << "Warning: --inplace has no effect when reading from stdin\n";
    }

    if (files.empty()) {
      LexContext ctx;
      auto tokens = ctx.lex_file("<stdin>");
      auto result = format::format(tokens, style);
      for (const auto& warning : result.warnings) {
        printWarning(std::cerr, "<stdin>", warning);
      }
      std::cout << result.formatted_text;
      return 0;
    }
    runFormatter(files, style, run, {.out = &std::cout, .err = &std::cerr});
    return 0;
  } catch (const std::exception& e) {
    std::cerr << "Error: " << e.what() << "\n";
    return 1;
  }
}
