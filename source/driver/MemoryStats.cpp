//------------------------------------------------------------------------------
// MemoryStats.cpp
// Utility for writing report of compiler memory usage
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/MemoryStats.h"

#include <algorithm>
#include <fmt/format.h>
#include <fstream>
#include <iostream>

#include "slang/analysis/AnalysisManager.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/OS.h"

namespace slang::driver {

using namespace analysis;
using namespace ast;
using namespace parsing;
using namespace syntax;

namespace {

static std::string formatBytes(size_t bytes) {
    if (bytes >= 1ull << 30)
        return fmt::format("{:.2f} GB", double(bytes) / double(1ull << 30));
    if (bytes >= 1ull << 20)
        return fmt::format("{:.2f} MB", double(bytes) / double(1ull << 20));
    if (bytes >= 1ull << 10)
        return fmt::format("{:.2f} KB", double(bytes) / double(1ull << 10));
    return fmt::format("{} B", bytes);
}

struct NodeKindEntry {
    std::string_view name;
    size_t count = 0;
    size_t bytes = 0;
    size_t tokenBytes = 0;
    size_t triviaBytes = 0;
};

// Walk all SyntaxNodes in a tree, accumulating per-SyntaxKind instance counts,
// node sizes, and the token/trivia bytes directly owned by each node kind.
// Tokens are attributed to their immediate parent node (not recursively).
struct CSTStatsVisitor : public SyntaxVisitor<CSTStatsVisitor> {
    flat_hash_map<SyntaxKind, NodeKindEntry> syntaxKinds;
    size_t totalTokenCount = 0;
    size_t totalTokenBytes = 0;
    size_t totalTriviaCount = 0;
    size_t totalTriviaBytes = 0;

    template<typename T>
    void handle(const T& node) {
        auto& e = syntaxKinds[node.kind];
        if (e.name.empty())
            e.name = toString(node.kind);
        e.count++;
        e.bytes += sizeof(T);

        // Attribute each direct child token (and its trivia) to this node kind.
        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            if (auto tok = node.childToken(i)) {
                auto tokenBytes = tok.getSizeInBytes();
                e.tokenBytes += tokenBytes;
                totalTokenBytes += tokenBytes;
                totalTokenCount++;

                auto trivia = tok.trivia();
                auto triviaBytes = trivia.size() * sizeof(Trivia);
                e.triviaBytes += triviaBytes;
                totalTriviaBytes += triviaBytes;
                totalTriviaCount += trivia.size();
            }
        }

        visitDefault(node);
    }
};

// Walk the full compiled AST, accumulating per-kind counts and sizes for
// symbols, expressions, and statements.
struct ASTStatsVisitor : public ASTVisitor<ASTStatsVisitor, VisitFlags::AllGood> {
    flat_hash_map<SymbolKind, NodeKindEntry> symbolKinds;
    flat_hash_map<ExpressionKind, NodeKindEntry> exprKinds;
    flat_hash_map<StatementKind, NodeKindEntry> stmtKinds;

    template<typename T>
    void handle(const T& node) {
        if constexpr (std::is_base_of_v<Symbol, T>) {
            auto& e = symbolKinds[node.kind];
            if (e.name.empty())
                e.name = toString(node.kind);
            e.count++;
            e.bytes += sizeof(T);
        }
        else if constexpr (std::is_base_of_v<Expression, T>) {
            auto& e = exprKinds[node.kind];
            if (e.name.empty())
                e.name = toString(node.kind);
            e.count++;
            e.bytes += sizeof(T);
        }
        else if constexpr (std::is_base_of_v<Statement, T>) {
            auto& e = stmtKinds[node.kind];
            if (e.name.empty())
                e.name = toString(node.kind);
            e.count++;
            e.bytes += sizeof(T);
        }
        visitDefault(node);
    }
};

static void printASTTable(std::ostream& out, std::vector<NodeKindEntry>& entries) {
    out << fmt::format("  {:<45}  {:>10}  {:>12}\n", "Kind", "Count", "Node Bytes");
    out << fmt::format("  {:-<45}  {:-<10}  {:-<12}\n", "", "", "");
    for (auto& e : entries)
        out << fmt::format("  {:<45}  {:>10}  {:>12}\n", e.name, e.count, formatBytes(e.bytes));
}

static void printCSTTable(std::ostream& out, std::vector<NodeKindEntry>& entries) {
    out << fmt::format("  {:<45}  {:>10}  {:>12}  {:>12}  {:>12}\n", "Kind", "Count", "Node Bytes",
                       "Token Bytes", "Trivia Bytes");
    out << fmt::format("  {:-<45}  {:-<10}  {:-<12}  {:-<12}  {:-<12}\n", "", "", "", "", "");
    for (auto& e : entries) {
        out << fmt::format("  {:<45}  {:>10}  {:>12}  {:>12}  {:>12}\n", e.name, e.count,
                           formatBytes(e.bytes), formatBytes(e.tokenBytes),
                           formatBytes(e.triviaBytes));
    }
}

template<typename TKey>
static void printTable(std::ostream& out, flat_hash_map<TKey, NodeKindEntry>& table,
                       std::string_view header, bool isCST = false) {
    std::vector<NodeKindEntry> entries;
    entries.reserve(table.size());
    for (auto& [_, e] : table)
        entries.push_back(e);

    if (entries.empty())
        return;

    std::sort(entries.begin(), entries.end(),
              [](const NodeKindEntry& a, const NodeKindEntry& b) { return a.bytes > b.bytes; });

    out << header << "\n";
    if (isCST)
        printCSTTable(out, entries);
    else
        printASTTable(out, entries);
    out << "\n";
}

} // namespace

void printMemoryStats(const std::string& fileName, const SourceManager& sourceManager,
                      std::span<const std::shared_ptr<SyntaxTree>> syntaxTrees,
                      const Compilation* compilation, const AnalysisManager* analysisManager) {
    std::ofstream fileStream;
    std::ostream* out;

    if (fileName == "-") {
        out = &std::cout;
    }
    else {
        fileStream.open(fileName);
        fileStream.exceptions(std::ios::failbit | std::ios::badbit);
        out = &fileStream;
    }

    const uint64_t peakBytes = OS::getPeakMemoryBytes();
    const size_t sourceBytes = sourceManager.getMemoryUsage();
    const size_t numBuffers = sourceManager.getAllBuffers().size();

    size_t cstBytes = 0;
    CSTStatsVisitor cstVisitor;
    for (auto& tree : syntaxTrees) {
        cstBytes += tree->allocator().getTotalBytesAllocated();
        tree->root().visit(cstVisitor);
    }

    size_t astBytes = 0;
    ASTStatsVisitor astVisitor;
    if (compilation) {
        astBytes = compilation->getTotalBytesAllocated();
        compilation->getRootNoFinalize().visit(astVisitor);
    }

    AnalysisManager::Stats analysisStats;
    if (analysisManager)
        analysisStats = analysisManager->getStats();

    *out << "Memory Usage Report\n";
    *out << "===================\n\n";

    *out << "Source files\n";
    *out << fmt::format("  Buffers: {:>12}\n", numBuffers);
    *out << fmt::format("  Memory:  {:>12}\n", formatBytes(sourceBytes));
    *out << "\n";

    *out << "CST\n";
    *out << fmt::format("  Syntax trees: {:>12} [{}]\n", syntaxTrees.size(), formatBytes(cstBytes));
    *out << fmt::format("  Tokens:       {:>12} [{}]\n", cstVisitor.totalTokenCount,
                        formatBytes(cstVisitor.totalTokenBytes));
    *out << fmt::format("  Trivia:       {:>12} [{}]\n", cstVisitor.totalTriviaCount,
                        formatBytes(cstVisitor.totalTriviaBytes));
    *out << "\n";
    printTable(*out, cstVisitor.syntaxKinds, "  Syntax node breakdown:", true);

    if (compilation) {
        *out << "AST\n";
        *out << fmt::format("  Compilation memory:   {:>12}\n\n", formatBytes(astBytes));

        printTable(*out, astVisitor.symbolKinds, "  Symbol breakdown:");
        printTable(*out, astVisitor.exprKinds, "  Expression breakdown:");
        printTable(*out, astVisitor.stmtKinds, "  Statement breakdown:");
    }

    if (analysisManager) {
        *out << "Analysis:\n";
        *out << fmt::format("  Memory usage: {:>12}\n", formatBytes(analysisStats.memoryUsage));
        *out << fmt::format("  Procedures:   {:>12}\n", analysisStats.numProcedures);
        *out << fmt::format("  Assertions:   {:>12}\n", analysisStats.numAssertions);
        *out << fmt::format("  Scopes:       {:>12}\n", analysisStats.numScopes);
        *out << "\n";
    }

    size_t totalTracked = sourceBytes + cstBytes + astBytes + analysisStats.memoryUsage;

    constexpr int labelWidth = 44;
    constexpr int valueWidth = 12;
    *out << std::string(labelWidth + valueWidth, '-') << "\n";
    *out << fmt::format("{:<{}}{:>{}}\n", "Total (tracked):", labelWidth, formatBytes(totalTracked),
                        valueWidth);
    *out << fmt::format("{:<{}}{:>{}}\n", "Peak process memory:", labelWidth,
                        formatBytes(peakBytes), valueWidth);
    *out << "\n";
}

} // namespace slang::driver
