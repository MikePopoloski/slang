#include "slang/ast/Compilation.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/driver/Driver.h"
#include "slang/util/VersionInfo.h"

using namespace slang;
using namespace slang::driver;
using namespace slang::ast;

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
        printf("slang version %d.%d.%d+%s\n", VersionInfo::getMajor(),
            VersionInfo::getMinor(), VersionInfo::getPatch(),
            std::string(VersionInfo::getHash()).c_str());
        return 0;
    }

    if (!driver.processOptions())
        return 2;

    bool ok = driver.parseAllSources();

    auto compilation = driver.createCompilation();

    std::string path;
    auto instances = compilation->getRoot().topInstances;
    for (auto& i: instances)
        i->visit(makeVisitor([&](auto& visitor, const InstanceSymbol& type) {
            if (type.isModule()) {
                std::string tmp_path;
                type.getHierarchicalPath(tmp_path);
                OS::print(fmt::fg(fmt::color::yellow_green),
                            fmt::format("Instance (Module): {} ({})\n", tmp_path, type.getDefinition().name));
                visitor.visitDefault(type);
            }
        }));

    ok &= driver.reportCompilation(*compilation, /* quiet */ false);

    return ok ? 0 : 3;
}
