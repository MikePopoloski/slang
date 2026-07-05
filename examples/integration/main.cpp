// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "slang/ast/Compilation.h"
#include "slang/driver/Driver.h"
#include "slang/util/VersionInfo.h"

using namespace slang;
using namespace slang::driver;

int main(int argc, char** argv) {
    Driver driver;
    driver.addStandardArgs();

    std::optional<bool> showHelp;
    std::optional<bool> showVersion;
    driver.cmdLine.add("-h,--help", showHelp, "Display available options");
    driver.cmdLine.add("--version", showVersion, "Display version information and exit");

    if (!driver.parseCommandLine(argc, argv))
        return 1;

    if (showHelp == true) {
        printf("%s\n", driver.cmdLine.getHelpText("slang SystemVerilog compiler").c_str());
        return 0;
    }

    if (showVersion == true) {
        printf("slang version %d.%d.%d+%s\n", VersionInfo::getMajor(), VersionInfo::getMinor(),
               VersionInfo::getPatch(), std::string(VersionInfo::getHash()).c_str());
        return 0;
    }

    if (!driver.processOptions())
        return 2;

    bool ok = driver.parseAllSources();
    ok &= driver.runFullCompilation();

    return ok ? 0 : 3;
}
