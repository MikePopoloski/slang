//------------------------------------------------------------------------------
//! @file netlist.cpp
//! @brief The slang netlist tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Netlist.h"

#include "NetlistVisitor.h"
#include "PathFinder.h"
#include "SplitVariables.h"
#include "fmt/color.h"
#include "fmt/format.h"
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <unordered_set>
#include <utility>
#include <vector>

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/driver/Driver.h"
#include "slang/text/FormatBuffer.h"
#include "slang/text/Json.h"
#include "slang/util/String.h"
#include "slang/util/TimeTrace.h"
#include "slang/util/Util.h"
#include "slang/util/Version.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::driver;
using namespace netlist;

namespace slang::diag {

inline constexpr DiagCode VariableReference(DiagSubsystem::Netlist, 0);

} // namespace slang::diag

void writeToFile(std::string_view fileName, std::string_view contents);

void printJson(Compilation& compilation, const std::string& fileName,
               const std::vector<std::string>& scopes) {
    JsonWriter writer;
    writer.setPrettyPrint(true);
    ASTSerializer serializer(compilation, writer);
    if (scopes.empty()) {
        serializer.serialize(compilation.getRoot());
    }
    else {
        for (auto& scopeName : scopes) {
            auto sym = compilation.getRoot().lookupName(scopeName);
            if (sym) {
                serializer.serialize(*sym);
            }
        }
    }
    writeToFile(fileName, writer.view());
}

void printDOT(const Netlist& netlist, const std::string& fileName) {
    slang::FormatBuffer buffer;
    buffer.append("digraph {\n");
    buffer.append("  node [shape=record];\n");
    for (auto& node : netlist) {
        switch (node->kind) {
            case NodeKind::PortDeclaration: {
                auto& portDecl = node->as<NetlistPortDeclaration>();
                buffer.format("  N{} [label=\"Port declaration\\n{}\"]\n", node->ID,
                              portDecl.hierarchicalPath);
                break;
            }
            case NodeKind::VariableDeclaration: {
                auto& varDecl = node->as<NetlistVariableDeclaration>();
                buffer.format("  N{} [label=\"Variable declaration\\n{}\"]\n", node->ID,
                              varDecl.hierarchicalPath);
                break;
            }
            case NodeKind::VariableAlias: {
                auto& varAlias = node->as<NetlistVariableAlias>();
                buffer.format("  N{} [label=\"Variable alias\\n{}\"]\n", node->ID,
                              varAlias.hierarchicalPath);
                break;
            }
            case NodeKind::VariableReference: {
                auto& varRef = node->as<NetlistVariableReference>();
                buffer.format("  N{} [label=\"{}\\n{}\"]\n", node->ID, varRef.toString(),
                              varRef.isLeftOperand() ? "[Assigned to]" : "");
                break;
            }
            default:
                SLANG_UNREACHABLE;
        }
    }
    for (auto& node : netlist) {
        for (auto& edge : node->getEdges()) {
            if (!edge->disabled) {
                buffer.format("  N{} -> N{}\n", node->ID, edge->getTargetNode().ID);
            }
        }
    }
    buffer.append("}\n");
    writeToFile(fileName, buffer.data());
}

template<typename Stream, typename String>
void writeToFile(Stream& os, std::string_view fileName, String contents) {
    os.write(contents.data(), contents.size());
    os.flush();
    if (!os) {
        SLANG_THROW(std::runtime_error(fmt::format("Unable to write to '{}'", fileName)));
    }
}

#if defined(_WIN32)

void writeToFile(std::string_view fileName, std::string_view contents) {
    if (fileName == "-") {
        writeToFile(std::wcout, "stdout", widen(contents));
    }
    else {
        std::ofstream file(widen(fileName));
        writeToFile(file, fileName, contents);
    }
}

#else

void writeToFile(std::string_view fileName, std::string_view contents) {
    if (fileName == "-") {
        writeToFile(std::cout, "stdout", contents);
    }
    else {
        std::ofstream file{std::string(fileName)};
        writeToFile(file, fileName, contents);
    }
}

#endif

void reportPath(Compilation& compilation, const NetlistPath& path) {
    DiagnosticEngine diagEngine(*compilation.getSourceManager());
    diagEngine.setMessage(diag::VariableReference, "variable {}");
    diagEngine.setSeverity(diag::VariableReference, DiagnosticSeverity::Note);
    auto textDiagClient = std::make_shared<TextDiagnosticClient>();
    textDiagClient->showColors(true);
    textDiagClient->showLocation(true);
    textDiagClient->showSourceLine(true);
    textDiagClient->showHierarchyInstance(true);
    diagEngine.addClient(textDiagClient);
    for (auto* node : path) {
        auto* SM = compilation.getSourceManager();
        auto& location = node->symbol.location;
        auto bufferID = location.buffer();
        SLANG_ASSERT(node->kind == NodeKind::VariableReference);
        const auto& varRefNode = node->as<NetlistVariableReference>();
        Diagnostic diagnostic(diag::VariableReference, varRefNode.expression.sourceRange.start());
        diagnostic << varRefNode.expression.sourceRange;
        if (varRefNode.isLeftOperand()) {
            diagnostic << fmt::format("{} assigned to", varRefNode.getName());
        }
        else {
            diagnostic << fmt::format("{} read from", varRefNode.getName());
        }
        diagEngine.issue(diagnostic);
        OS::print(fmt::format("{}\n", textDiagClient->getString()));
        textDiagClient->clear();
    }
}

int main(int argc, char** argv) {

    driver::Driver driver;
    driver.addStandardArgs();

    std::optional<bool> showHelp;
    std::optional<bool> showVersion;
    std::optional<bool> quiet;
    std::optional<bool> debug;
    driver.cmdLine.add("-h,--help", showHelp, "Display available options");
    driver.cmdLine.add("--version", showVersion, "Display version information and exit");
    driver.cmdLine.add("-q,--quiet", quiet, "Suppress non-essential output");
    driver.cmdLine.add("-d,--debug", debug, "Output debugging information");

    std::optional<std::string> astJsonFile;
    driver.cmdLine.add(
        "--ast-json", astJsonFile,
        "Dump the compiled AST in JSON format to the specified file, or '-' for stdout", "<file>",
        CommandLineFlags::FilePath);

    std::vector<std::string> astJsonScopes;
    driver.cmdLine.add("--ast-json-scope", astJsonScopes,
                       "When dumping AST to JSON, include only the scopes specified by the "
                       "given hierarchical paths",
                       "<path>");

    std::optional<std::string> netlistDotFile;
    driver.cmdLine.add("--netlist-dot", netlistDotFile,
                       "Dump the netlist in DOT format to the specified file, or '-' for stdout",
                       "<file>", CommandLineFlags::FilePath);

    std::optional<std::string> fromPointName;
    driver.cmdLine.add("--from", fromPointName, "Specify a start point from which to trace a path",
                       "<name>");

    std::optional<std::string> toPointName;
    driver.cmdLine.add("--to", toPointName, "Specify a finish point to trace a path to", "<name>");

    if (!driver.parseCommandLine(argc, argv)) {
        return 1;
    }

    if (showHelp == true) {
        std::cout << fmt::format(
            "{}\n", driver.cmdLine.getHelpText("slang SystemVerilog netlist tool").c_str());
        return 0;
    }

    if (showVersion == true) {
        std::cout << fmt::format("slang-netlist version {}.{}.{}+{}\n", VersionInfo::getMajor(),
                                 VersionInfo::getMinor(), VersionInfo::getPatch(),
                                 std::string(VersionInfo::getHash()).c_str());
        return 0;
    }

    if (!driver.processOptions()) {
        return 2;
    }

    if (debug) {
        Config::getInstance().debugEnabled = true;
    }

    SLANG_TRY {

        bool ok = driver.parseAllSources();

        auto compilation = driver.createCompilation();
        ok &= driver.reportCompilation(*compilation, *quiet);

        if (!ok) {
            return ok;
        }

        if (astJsonFile) {
            printJson(*compilation, *astJsonFile, astJsonScopes);
            return 0;
        }

        // Create the netlist by traversing the AST.
        Netlist netlist;
        NetlistVisitor visitor(*compilation, netlist);
        compilation->getRoot().visit(visitor);
        SplitVariables splitVariables(netlist);
        DEBUG_PRINT(fmt::format("Netlist has {} nodes and {} edges\n", netlist.numNodes(),
                                netlist.numEdges()));

        // Output a DOT file of the netlist.
        if (netlistDotFile) {
            printDOT(netlist, *netlistDotFile);
            return 0;
        }

        // Find a point-to-point path in the netlist.
        if (fromPointName.has_value() && toPointName.has_value()) {
            if (!fromPointName.has_value()) {
                SLANG_THROW(std::runtime_error("please specify a start point using --from <name>"));
            }
            if (!toPointName.has_value()) {
                SLANG_THROW(std::runtime_error("please specify a finish point using --to <name>"));
            }
            auto fromPoint = netlist.lookupVariable(*fromPointName);
            if (fromPoint == nullptr) {
                SLANG_THROW(std::runtime_error(
                    fmt::format("could not find start point: {}", *fromPointName)));
            }
            auto toPoint = netlist.lookupVariable(*toPointName);
            if (toPoint == nullptr) {
                SLANG_THROW(std::runtime_error(
                    fmt::format("could not find finish point: {}", *toPointName)));
            }
            PathFinder pathFinder(netlist);
            auto path = pathFinder.find(*fromPoint, *toPoint);
            if (path.empty()) {
                SLANG_THROW(std::runtime_error(
                    fmt::format("no path between {} and {}", *fromPointName, *toPointName)));
            }
            // Report the path.
            reportPath(*compilation, path);
        }

        // No action performed.
        return 1;
    }
    SLANG_CATCH(const std::exception& e) {
#if __cpp_exceptions
        OS::printE(fmt::format("{}\n", e.what()));
#endif
        return 1;
    }

    return 0;
}
