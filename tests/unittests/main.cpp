#define CATCH_CONFIG_RUNNER
#include "Catch/catch.hpp"

// This file contains the Catch unit testing framework implementation
// as well as the main() function, with command line arg parsing.
//
// See documentation at: https://github.com/philsquared/Catch
//
// Don't put tests in this file; we want to avoid recompiling the
// Catch impl whenever we modify a test.

#include "fmt/format.h"

#include "util/BumpAllocator.h"
#include "diagnostics/Diagnostics.h"

namespace slang {

BumpAllocator alloc;
Diagnostics diagnostics;

}

ppk::assert::implementation::AssertAction::AssertAction
assertionHandler(const char* file, int line, const char* function,
                 const char* expression, int, const char* message) {

    std::string report = fmt::format("Assertion '{}' failed\n  in file {}, line {}\n"
                                     "  function: {}\n",
                                     expression, file, line, function);
    if (message)
        report += fmt::format("  with message: {}\n\n", message);

    throw ppk::assert::AssertionException(file, line, function, expression, report.c_str());
}

int main(int argc, char* argv[]) {
    // Install a custom handler for assertions so that they always just throw.
    ppk::assert::implementation::setAssertHandler(assertionHandler);

    int result = Catch::Session().run(argc, argv);
    return result < 0xff ? result : 0xff;
}