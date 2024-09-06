//------------------------------------------------------------------------------
//! @file hier.cpp
//! @brief A tool for printing information about a Verilog hierarchy
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include <algorithm>
#include <regex>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/driver/Driver.h"
#include "slang/util/VersionInfo.h"

using namespace slang;
using namespace slang::driver;
using namespace slang::ast;

int main(int argc, char** argv) {
    std::regex regex;
    std::smatch match;
    Driver driver;
    driver.addStandardArgs();

    std::optional<bool> showHelp;
    std::optional<bool> showVersion;
    std::optional<bool> params;
    std::optional<int> maxDepth;
    std::optional<std::string> instPrefix;
    std::optional<std::string> instRegex;
    std::optional<std::string> customFormat;
    driver.cmdLine.add("-h,--help", showHelp, "Display available options");
    driver.cmdLine.add("--version", showVersion, "Display version information and exit");
    driver.cmdLine.add("--params", params, "Display instance parameter values");
    driver.cmdLine.add("--max-depth", maxDepth, "Maximum instance depth to be printed", "<depth>");
    driver.cmdLine.add("--inst-prefix", instPrefix,
                       "Skip all instance subtrees not under this prefix (inst.sub_inst...)",
                       "<inst-prefix>");
    driver.cmdLine.add("--inst-regex", instRegex,
                       "Show only instances matched by regex (scans whole tree)", "<inst-regex>");
    driver.cmdLine.add(
        "--custom-format", customFormat,
        "Use libfmt-style strings to format output with {inst}, {module}, {file} as argument names",
        "<fmt::format string>");

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

    auto compilation = driver.createCompilation();
    auto sourceManager = compilation->getSourceManager();

    if (instRegex.has_value())
        regex = instRegex.value();
    auto instances = compilation->getRoot().topInstances;
    for (auto& i : instances) {
        int depth = maxDepth.value_or(-1); // will never be 0, go full depth
        int pathLength = instPrefix.value_or("").length();
        int index = 0;
        i->visit(makeVisitor([&](auto& visitor, const InstanceSymbol& type) {
            if (type.isModule()) {
                std::string s_inst;
                int len = type.name.length();
                int save_index = index;
                // if no instPrefix, pathLength is 0, and this check will never take place, so
                // instPrefix.value() is safe if index >= pathLength we satisfied the full
                // instPrefix. from now on we are limited only by max-depth
                if (index < pathLength) {
                    if (type.name !=
                        instPrefix.value().substr(index, std::min(pathLength - index, len))) {
                        // current instance name did not match
                        return;
                    }
                    index += len;
                    if (index < pathLength && instPrefix.value()[index] != '.')
                        return; // separator needed, but didn't find one
                    index++;    // adjust for '.'
                }
                type.getHierarchicalPath(s_inst);
                if (!instRegex.has_value() || std::regex_search(s_inst, match, regex)) {
                    auto s_module = type.getDefinition().name;
                    auto s_file = sourceManager->getFileName(type.getDefinition().location);
                    if (customFormat.has_value())
                        OS::print(fmt::format(fmt::runtime(customFormat.value()),
                                              fmt::arg("module", s_module),
                                              fmt::arg("inst", s_inst), fmt::arg("file", s_file)));
                    else
                        OS::print(fmt::format("Module=\"{}\" Instance=\"{}\" File=\"{}\" ",
                                              s_module, s_inst, s_file));
                    int size = type.body.getParameters().size();
                    if (size && params.value_or(false)) {
                        OS::print(fmt::format("Parameters: "));
                        for (auto p : type.body.getParameters()) {
                            std::string v;
                            size--;
                            if (p->symbol.kind == SymbolKind::Parameter)
                                v = p->symbol.as<ParameterSymbol>().getValue().toString();
                            else if (p->symbol.kind == SymbolKind::TypeParameter)
                                v = p->symbol.as<TypeParameterSymbol>()
                                        .targetType.getType()
                                        .toString();
                            else
                                v = "?";
                            OS::print(fmt::format("{}={}{}", p->symbol.name, v, size ? ", " : ""));
                        }
                    }
                    OS::print("\n");
                }
                depth--;
                if (depth)
                    visitor.visitDefault(type);
                depth++;
                index = save_index;
            }
        }));
    }
    ok &= driver.reportCompilation(*compilation, /* quiet */ false);

    return ok ? 0 : 3;
}
