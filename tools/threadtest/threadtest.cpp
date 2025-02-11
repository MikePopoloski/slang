//------------------------------------------------------------------------------
// slang_threadtest.cpp
// Testing tool for multithreaded AST visitation
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include <BS_thread_pool.hpp>

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/driver/Driver.h"
#include "slang/text/Json.h"

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
        driver.reportCompilation(*compilation, true);
        if (!driver.reportDiagnostics(true))
            return 2;

        compilation->freeze();

        BS::thread_pool threadPool;
        threadPool.detach_blocks(0, count.value_or(1000), [&](int from, int to) {
            SLANG_TRY {
                JsonWriter writer;
                ASTSerializer serializer(*compilation, writer);
                serializer.setTryConstantFold(false);

                serializer.startArray();
                for (int i = from; i < to; i++)
                    serializer.serialize(compilation->getRoot());
                serializer.endArray();
            }
            SLANG_CATCH(const std::exception& e) {
                SLANG_REPORT_EXCEPTION(e, "{}\n");
            }
        });

        return 0;
    }
    SLANG_CATCH(const std::exception& e) {
        SLANG_REPORT_EXCEPTION(e, "{}\n");
    }
    return 3;
}
