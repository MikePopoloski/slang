//------------------------------------------------------------------------------
// slang_main.cpp
// Testing tool for multithreaded AST visitation
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/driver/Driver.h"
#include "slang/text/Json.h"
#include "slang/util/ThreadPool.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::driver;

int main(int argc, char** argv) {
    SLANG_TRY {
        OS::setupConsole();
        OS::tryEnableColors();

        Driver driver;
        driver.addStandardArgs();

        std::optional<int> count;
        driver.cmdLine.add("-n,--count", count, "Number of iterations to perform");

        if (!driver.parseCommandLine(argc, argv) || !driver.processOptions() ||
            !driver.parseAllSources()) {
            return 1;
        }

        auto compilation = driver.createCompilation();
        if (!driver.reportCompilation(*compilation, true))
            return 2;

        ThreadPool threadPool;
        threadPool.pushLoop(0, count.value_or(1000), [&](int from, int to) {
            SLANG_TRY {
                JsonWriter writer;
                ASTSerializer serializer(*compilation, writer);
                serializer.setTryConstantFold(false);

                serializer.startArray();
                for (int i = from; i < to; i++)
                    serializer.serialize(compilation->getRoot());
                serializer.endArray();
            }
            SLANG_CATCH(...) {
#if defined(SLANG_USE_CPPTRACE)
                cpptrace::from_current_exception().print();
#endif
                throw;
            }
        });

        return 0;
    }
    SLANG_CATCH(const std::exception& e) {
#if __cpp_exceptions
        OS::printE(fmt::format("{}\n", e.what()));
#    if defined(SLANG_USE_CPPTRACE)
        cpptrace::from_current_exception().print();
#    endif
#endif
    }
    return 3;
}
