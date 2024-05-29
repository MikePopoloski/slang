//------------------------------------------------------------------------------
//! @file NetlistVisitor.h
//! @brief An AST visitor (and sub visitors) to construct a netlist
//         representation.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "fmt/color.h"
#include "fmt/format.h"
#include <algorithm>
#include <iostream>

#include "slang/ast/ASTContext.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/util/Util.h"

#include "Config.h"
#include "Debug.h"
#include "Netlist.h"
#include "visitors/InstanceVisitor.hpp"

using namespace slang;

namespace netlist {

/// The top-level visitor that traverses the AST and builds a netlist connectivity graph.
class NetlistVisitor : public ast::ASTVisitor<NetlistVisitor, true, false> {
public:
    explicit NetlistVisitor(ast::Compilation& compilation, Netlist& netlist) :
        compilation(compilation), netlist(netlist) {}

    void handle(const ast::InstanceSymbol& symbol) {
        InstanceVisitor visitor(compilation, netlist);
        symbol.visit(visitor);
    }

private:
    ast::Compilation& compilation;
    Netlist& netlist;
};

} // namespace netlist
