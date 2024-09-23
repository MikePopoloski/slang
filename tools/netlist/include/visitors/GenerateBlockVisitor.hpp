//------------------------------------------------------------------------------
//! @file GenerateBlockVisitor.h
//! @brief Visit generate blocks as part of the construction of a netlist graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "visitors/ContinuousAssignVisitor.hpp"
#include "visitors/ProceduralBlockVisitor.hpp"

using namespace slang;

namespace netlist {

/// Visit generate blocks. When slang elaborates the design, generate loops are unrolled
/// and conditionals evaluated. Branches in a condition that are not taken are
/// marked as uninstantiated, and are therefore not visited.
class GenerateBlockVisitor : public ast::ASTVisitor<GenerateBlockVisitor, true, false> {
public:
    explicit GenerateBlockVisitor(ast::Compilation& compilation, Netlist& netlist,
                                  NetlistVisitorOptions const& options) :
        compilation(compilation), netlist(netlist), options(options) {}

    /// Variable declaration.
    void handle(const ast::VariableSymbol& symbol) { netlist.addVariableDeclaration(symbol); }

    /// Net declaration.
    void handle(const ast::NetSymbol& symbol) { netlist.addVariableDeclaration(symbol); }

    /// Procedural block.
    void handle(const ast::ProceduralBlockSymbol& symbol) {
        ProceduralBlockVisitor visitor(compilation, netlist, options, ast::EdgeKind::None);
        symbol.visit(visitor);
    }

    /// Continuous assignment statement.
    void handle(const ast::ContinuousAssignSymbol& symbol) {
        ast::EvalContext evalCtx(ast::ASTContext(compilation.getRoot(), ast::LookupLocation::max));
        SmallVector<NetlistNode*> condVars;
        ContinuousAssignVisitor visitor(netlist, evalCtx, condVars);
        symbol.visit(visitor);
    }

private:
    Netlist& netlist;
    NetlistVisitorOptions const& options;
    ast::Compilation& compilation;
};

} // namespace netlist
