//------------------------------------------------------------------------------
// CSTMemoryStats.cpp
// Memory usage statistics for the CST (Concrete Syntax Tree).
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/CSTMemoryStats.h"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <ostream>
#include <string>
#include <vector>

#include "slang/driver/Driver.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/MemStatsUtil.h"

using namespace slang;
using namespace slang::syntax;
using namespace slang::parsing;
using namespace slang::driver;

// Walks every syntax node and accumulates memory per SyntaxKind and per
// enclosing module/package/interface/program scope.
//
// Accounting rules:
//   - Concrete non-list nodes: node.getSize() = sizeof(T)
//                              + getReferencedSize() for each direct Token member
//     Embedded list structs (SyntaxList, SeparatedSyntaxList, TokenList) are part
//     of sizeof(T); their span arrays and element contents are not included here.
//   - Child SyntaxNode pointer members: visited and counted separately by the visitor.
//   - List nodes (SyntaxList / SeparatedSyntaxList / TokenList): NOT tracked as
//     separate nodes; sizeof is already part of the parent.  The visitor still
//     walks into them so tokens are picked up by visitToken().
//   - Token Info blocks and trivia arrays: tracked separately via visitToken().
struct CSTMemVisitor : public SyntaxVisitor<CSTMemVisitor> {
    struct KindStats {
        size_t count = 0;
        size_t bytes = 0;
    };
    std::map<SyntaxKind, KindStats> kindStats;
    std::map<std::string, size_t> scopeBytes;
    std::vector<std::string> scopeStack;

    size_t totalTokenBytes = 0;  // sizeof(Token) + Info block + trivia array per token
    size_t totalTriviaBytes = 0; // trivia array bytes (subset of totalTokenBytes)

    std::string currentScope() const {
        return scopeStack.empty() ? "<toplevel>" : scopeStack.back();
    }

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4702) // unreachable code
#endif
    // Catch-all for all concrete syntax node types and list nodes.
    template<typename T>
    void handle(const T& node) {
        if constexpr (std::is_base_of_v<SyntaxListBase, T>) {
            // List sizes are included in the parent node's getSize().
            // Still walk children so tokens are tracked via visitToken().
            visitDefault(node);
            return;
        }
        size_t sz = node.getSize();
        kindStats[node.kind].count++;
        kindStats[node.kind].bytes += sz;
        scopeBytes[currentScope()] += sz;
        visitDefault(node);
    }
#ifdef _MSC_VER
#    pragma warning(pop)
#endif

    // Specific handler for module/interface/program/package declarations:
    // push a new scope name before recursing into children.
    void handle(const ModuleDeclarationSyntax& node) {
        std::string name = std::string(node.header->name.valueText());
        if (!scopeStack.empty())
            name = scopeStack.back() + "." + name;

        size_t sz = node.getSize();
        kindStats[node.kind].count++;
        kindStats[node.kind].bytes += sz;
        scopeBytes[name] += sz;

        scopeStack.push_back(name);
        visitDefault(node);
        scopeStack.pop_back();
    }

    // Track token Info blocks and trivia arrays separately.
    void visitToken(Token token) {
        if (!token.valid())
            return;
        totalTokenBytes += sizeof(Token) + token.getReferencedSize();
        totalTriviaBytes += token.getTriviaArraySize();
    }
};

void printCSTMemoryStats(Driver& driver, const std::string& fileName) {
    std::ofstream fileStream;
    std::ostream* outPtr;
    if (fileName == "-") {
        outPtr = &std::cout;
    }
    else {
        fileStream.open(fileName);
        fileStream.exceptions(std::ios::failbit | std::ios::badbit);
        outPtr = &fileStream;
    }
    std::ostream& out = *outPtr;
    size_t processRSS = memStatsGetProcessRSS();
    size_t syntaxTreeAllocBytes = 0;
    size_t libraryMapAllocBytes = 0;
    size_t totalNodeBytes = 0;

    CSTMemVisitor vis;

    auto accumTrees = [&](const auto& trees, size_t& allocBytes) {
        for (auto& tree : trees) {
            allocBytes += tree->allocator().getTotalAllocatedBytes();
            tree->root().visit(vis);
        }
    };

    accumTrees(driver.syntaxTrees, syntaxTreeAllocBytes);
    accumTrees(driver.sourceLoader.getLibraryMaps(), libraryMapAllocBytes);
    for (auto& [kind, ks] : vis.kindStats)
        totalNodeBytes += ks.bytes;

    size_t sourceManagerBytes = driver.sourceManager.getMemoryUsage();

    out << "\n--- CST (Concrete Syntax Tree) ---\n";
    if (processRSS > 0)
        out << fmt::format("{:>4}{:<28}: {}\n", "", "Process RSS", memStatsFmtBytes(processRSS));
    out << "\n  Driver Components:\n";
    out << fmt::format("{:>4}{:<28}: {}\n", "", "Source Manager",
                       memStatsFmtBytes(sourceManagerBytes));
    out << fmt::format("{:>4}{:<28}: {}\n", "", "Syntax Tree Allocators",
                       memStatsFmtBytes(syntaxTreeAllocBytes));
    out << fmt::format("{:>4}{:<28}: {}\n", "", "Library Map Allocators",
                       memStatsFmtBytes(libraryMapAllocBytes));
    out << "\n  Syntax Node Data:\n";
    out << fmt::format("{:>4}{:<28}: {}\n", "", "Total node memory",
                       memStatsFmtBytes(totalNodeBytes));
    out << fmt::format("{:>8}{:<28}: {}\n", "", "Total token memory",
                       memStatsFmtBytes(vis.totalTokenBytes));
    out << fmt::format("{:>12}{:<28}: {}\n", "", "Total trivia memory",
                       memStatsFmtBytes(vis.totalTriviaBytes));

    // Per-kind breakdown, sorted by bytes descending.
    out << "\n  Node type breakdown (sorted by memory):\n";
    std::vector<std::pair<SyntaxKind, CSTMemVisitor::KindStats>> kindVec(vis.kindStats.begin(),
                                                                         vis.kindStats.end());
    std::sort(kindVec.begin(), kindVec.end(),
              [](const auto& a, const auto& b) { return a.second.bytes > b.second.bytes; });
    out << fmt::format("    {:<45} {:>10}  {:>10}  {:>12}\n", "Node Kind", "Count", "Total",
                       "Per Node");
    out << fmt::format("    {}\n", std::string(80, '-'));
    for (auto& [kind, ks] : kindVec) {
        size_t perNode = ks.count > 0 ? ks.bytes / ks.count : 0;
        out << fmt::format("    {:<45} {:>10}  {:>10}  {:>12}\n", toString(kind), ks.count,
                           memStatsFmtBytes(ks.bytes), memStatsFmtBytes(perNode));
    }

    // Per-module/package/scope breakdown, sorted by bytes descending.
    out << "\n  Module/Package/Scope breakdown (sorted by memory):\n";
    std::vector<std::pair<std::string, size_t>> scopeVec(vis.scopeBytes.begin(),
                                                         vis.scopeBytes.end());
    std::sort(scopeVec.begin(), scopeVec.end(),
              [](const auto& a, const auto& b) { return a.second > b.second; });
    out << fmt::format("    {:<50} {:>15}\n", "Scope", "Node Memory");
    out << fmt::format("    {}\n", std::string(70, '-'));
    for (auto& [scope, bytes] : scopeVec)
        out << fmt::format("    {:<50} {:>15}\n", scope, memStatsFmtBytes(bytes));

    out << "\n";
}
