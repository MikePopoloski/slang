//------------------------------------------------------------------------------
//! @file netlist.cpp
//! @brief The slang netlist tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "Netlist.h"

#include "CombLoops.h"
#include "PathFinder.h"
#include "fmt/color.h"
#include "fmt/format.h"
#include "visitors/NetlistVisitor.h"
#include <iostream>
#include <stdexcept>
#include <vector>

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/driver/Driver.h"
#include "slang/text/FormatBuffer.h"
#include "slang/text/Json.h"
#include "slang/util/Util.h"
#include "slang/util/VersionInfo.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::driver;
using namespace netlist;

template<>
class fmt::formatter<NetlistNode> {
public:
    constexpr auto parse(format_parse_context& ctx) { return ctx.begin(); }
    template<typename Context>
    constexpr auto format(NetlistNode const& node, Context& ctx) const {
        if (node.kind == NodeKind::VariableAlias) {
            auto& aliasNode = node.as<NetlistVariableAlias>();
            return fmt::format_to(ctx.out(), "{}{}", aliasNode.hierarchicalPath, aliasNode.overlap);
        }
        else if (node.kind == NodeKind::VariableDeclaration) {
            auto& declNode = node.as<NetlistVariableDeclaration>();
            return fmt::format_to(ctx.out(), "{}", declNode.hierarchicalPath);
        }
        else {
            return fmt::format_to(ctx.out(), "{}", node.getName());
        }
    }
};

namespace slang::diag {

inline constexpr DiagCode VariableReference(DiagSubsystem::Netlist, 0);

} // namespace slang::diag

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
    OS::writeFile(fileName, writer.view());
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
                if (!varRef.isLeftOperand())
                    buffer.format("  N{} [label=\"{}\\n\"]\n", node->ID, varRef.toString());
                else if (node->edgeKind == EdgeKind::None)
                    buffer.format("  N{} [label=\"{}\\n[Assigned to]\"]\n", node->ID,
                                  varRef.toString());
                else
                    buffer.format("  N{} [label=\"{}\\n[Assigned to @({})]\"]\n", node->ID,
                                  varRef.toString(), toString(node->edgeKind));
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
    OS::writeFile(fileName, buffer.str());
}

void reportPath(Compilation& compilation, const NetlistPath& path) {
    DiagnosticEngine diagEngine(*compilation.getSourceManager());
    diagEngine.setMessage(diag::VariableReference, "variable {}");
    diagEngine.setSeverity(diag::VariableReference, DiagnosticSeverity::Note);
    auto textDiagClient = std::make_shared<TextDiagnosticClient>();
    textDiagClient->showColors(true);
    textDiagClient->showLocation(true);
    textDiagClient->showSourceLine(true);
    textDiagClient->showHierarchyInstance(ShowHierarchyPathOption::Always);
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

void dumpCyclesList(Compilation& compilation, Netlist& netlist,
                    std::vector<CycleListType>* cycles) {
    auto s = cycles->size();
    if (!s) {
        OS::print("No combinatorial loops detected\n");
        return;
    }
    OS::print(fmt::format("Detected {} combinatorial loop{}:\n", s, (s > 1) ? "s" : ""));
    NetlistPath path;
    for (int i = 0; i < s; i++) {
        auto si = (*cycles)[i].size();
        for (int j = 0; j < si; j++) {
            auto& node = netlist.getNode((*cycles)[i][j]);
            if (node.kind == NodeKind::VariableReference) {
                path.add(node);
            }
        }
        OS::print(fmt::format("Path length: {}\n", path.size()));
        reportPath(compilation, path);
        path.clear();
    }
}

/// Exand a variable declaration node into a set of aliases if any are defined.
/// These are used for searching for paths.
auto expandVarDecl(NetlistVariableDeclaration* node) {
    std::vector<NetlistNode*> result;
    if (node->aliases.empty()) {
        result.push_back(node);
    }
    else {
        for (auto* alias : node->aliases) {
            result.push_back(alias);
        }
    }
    return result;
}

int main(int argc, char** argv) {
    OS::setupConsole();

    driver::Driver driver;
    driver.addStandardArgs();

    std::optional<bool> showHelp;
    std::optional<bool> showVersion;
    std::optional<bool> quiet;
    std::optional<bool> debug;
    std::optional<bool> combLoops;
    std::optional<bool> unrollForLoops;
    driver.cmdLine.add("-h,--help", showHelp, "Display available options");
    driver.cmdLine.add("--version", showVersion, "Display version information and exit");
    driver.cmdLine.add("-q,--quiet", quiet, "Suppress non-essential output");
    driver.cmdLine.add("-d,--debug", debug, "Output debugging information");
    driver.cmdLine.add("-c,--comb-loops", combLoops, "Detect combinatorial loops");
    driver.cmdLine.add("--unroll-for-loops", unrollForLoops, "Unroll procedural for loops");

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

    if (quiet) {
        Config::getInstance().quietEnabled = true;
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
        NetlistVisitorOptions options;
        options.unrollForLoops = unrollForLoops.value_or(false);
        NetlistVisitor visitor(*compilation, netlist, options);
        compilation->getRoot().visit(visitor);
        netlist.split();
        DEBUG_PRINT("Netlist has {} nodes and {} edges\n", netlist.numNodes(), netlist.numEdges());

        // Output a DOT file of the netlist.
        if (netlistDotFile) {
            printDOT(netlist, *netlistDotFile);
            return 0;
        }

        if (combLoops == true) {
            ElementaryCyclesSearch ecs(netlist);
            std::vector<CycleListType>* cycles = ecs.getElementaryCycles();
            dumpCyclesList(*compilation, netlist, cycles);
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

            // Expand the start and end points over aliases of the variable declaration nodes.
            auto startPoints = expandVarDecl(fromPoint);
            auto endPoints = expandVarDecl(toPoint);

            // Search through all combinations of start and end points. Report
            // the first path found and stop searching.
            for (auto* src : startPoints) {
                for (auto* dst : endPoints) {

                    DEBUG_PRINT("Searching for path between:\n  {}\n  {}\n", *src, *dst);

                    // Search for the path.
                    PathFinder pathFinder(netlist);
                    auto path = pathFinder.find(*src, *dst);

                    if (!path.empty()) {
                        // Report the path and exit.
                        reportPath(*compilation, path);
                        return 0;
                    }
                }
            }

            // No path found.
            SLANG_THROW(std::runtime_error(
                fmt::format("no path between {} and {}", *fromPointName, *toPointName)));
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
