#pragma once

#include "visitors/ProceduralBlockVisitor.hpp"

using namespace slang;

namespace netlist {

/// Visit generate blocks where new variable and net declarations can be
/// introduced.
class GenerateBlockVisitor : public ast::ASTVisitor<GenerateBlockVisitor, true, false> {
public:
    explicit GenerateBlockVisitor(ast::Compilation& compilation, Netlist& netlist) :
        compilation(compilation), netlist(netlist) {}

    /// Variable declaration.
    void handle(const ast::VariableSymbol& symbol) { netlist.addVariableDeclaration(symbol); }

    /// Net declaration.
    void handle(const ast::NetSymbol& symbol) { netlist.addVariableDeclaration(symbol); }

    /// Procedural block.
    void handle(const ast::ProceduralBlockSymbol& symbol) {
        ProceduralBlockVisitor visitor(compilation, netlist);
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
    ast::Compilation& compilation;
};

} // namespace netlist
