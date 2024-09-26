//------------------------------------------------------------------------------
//! @file NetlistVisitor.h
//! @brief An AST visitor to build a netlist graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Netlist.h"
#include "NetlistVisitorOptions.hpp"
#include "visitors/InstanceVisitor.hpp"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"

using namespace slang;

namespace netlist {

/// The top-level visitor that traverses the AST and builds a netlist connectivity graph.
class NetlistVisitor : public ast::ASTVisitor<NetlistVisitor, true, false> {
public:
    explicit NetlistVisitor(ast::Compilation& compilation, Netlist& netlist,
                            NetlistVisitorOptions const& options) :
        compilation(compilation), netlist(netlist), options(options) {}

    void handle(const ast::InstanceSymbol& symbol) {
        InstanceVisitor visitor(compilation, netlist, options);
        symbol.visit(visitor);
    }

private:
    ast::Compilation& compilation;
    Netlist& netlist;
    NetlistVisitorOptions const& options;
};

} // namespace netlist
