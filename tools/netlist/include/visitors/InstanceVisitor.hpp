//------------------------------------------------------------------------------
//! @file InstanceVisitor.h
//! @brief Visit instances as part of the construction of a netlist graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "visitors/ContinuousAssignVisitor.hpp"
#include "visitors/GenerateBlockVisitor.hpp"

using namespace slang;

namespace netlist {

/// Visit module and interface instances to dispatch visitors for procedural
/// blocks, generate blocks and continuous assignments. 
class InstanceVisitor : public ast::ASTVisitor<InstanceVisitor, true, false> {
public:
    explicit InstanceVisitor(ast::Compilation& compilation, Netlist& netlist,
                             NetlistVisitorOptions const& options) :
        compilation(compilation), netlist(netlist), options(options) {}

    /// Procedural block.
    void handle(const ast::ProceduralBlockSymbol& symbol) {
        ProceduralBlockVisitor visitor(compilation, netlist, options,
                                       ProceduralBlockVisitor::determineEdgeKind(symbol));
        symbol.visit(visitor);
    }

    /// Generate block.
    void handle(const ast::GenerateBlockSymbol& symbol) {
        if (!symbol.isUninstantiated) {
            GenerateBlockVisitor visitor(compilation, netlist, options);
            symbol.visit(visitor);
        }
    }

    /// Continuous assignment statement.
    void handle(const ast::ContinuousAssignSymbol& symbol) {
        ast::EvalContext evalCtx(ast::ASTContext(compilation.getRoot(), ast::LookupLocation::max));
        SmallVector<NetlistNode*> condVars;
        ContinuousAssignVisitor visitor(netlist, evalCtx, condVars);
        symbol.visit(visitor);
    }

private:
    ast::Compilation& compilation;
    Netlist& netlist;
    NetlistVisitorOptions const& options;
};

} // namespace netlist
