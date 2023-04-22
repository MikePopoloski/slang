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
#include <iostream>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"

#include "Netlist.h"

namespace slang {

/// An AST visitor to identify variable references with selectors in
/// expressions only.
class VariableReferenceVisitor : public ast::ASTVisitor<VariableReferenceVisitor, false, true> {
public:
  explicit VariableReferenceVisitor(Netlist &netlist,
                                    std::vector<NetlistNode*> &visitList,
                                    ast::EvalContext &evalCtx) :
    netlist(netlist), visitList(visitList), evalCtx(evalCtx) {}

  void handle(const ast::NamedValueExpression &expr) {
    auto &node = netlist.addVariableReference(expr.symbol);
    visitList.push_back(&node);
    for (auto *selector : selectors) {
      if (selector->kind == ast::ExpressionKind::ElementSelect) {
        auto index = selector->as<ast::ElementSelectExpression>().selector().eval(evalCtx);
        node.addElementSelect(index);
      }
      else if (selector->kind == ast::ExpressionKind::RangeSelect) {
        auto &rangeSelectExpr = selector->as<ast::RangeSelectExpression>();
        auto leftIndex = rangeSelectExpr.left().eval(evalCtx);
        auto rightIndex = rangeSelectExpr.right().eval(evalCtx);
        node.addRangeSelect(leftIndex, rightIndex);
      }
      else if (selector->kind == ast::ExpressionKind::MemberAccess) {
        node.addMemberAccess(selector->as<ast::MemberAccessExpression>().member.name);
      }
    }
    selectors.clear();
  }

  void handle(const ast::ElementSelectExpression &expr) {
    selectors.push_back(&expr);
    expr.value().visit(*this);
  }

  void handle(const ast::RangeSelectExpression &expr) {
    selectors.push_back(&expr);
    expr.value().visit(*this);
  }

  void handle(const ast::MemberAccessExpression &expr) {
    selectors.push_back(&expr);
    expr.value().visit(*this);
  }

private:
  Netlist &netlist;
  std::vector<NetlistNode*> &visitList;
  ast::EvalContext &evalCtx;
  std::vector<const ast::Expression*> selectors;
};

/// An AST visitor to create dependencies between occurrances of variables
/// appearing on the left and right hand sides of assignment statements.
class AssignmentVisitor : public ast::ASTVisitor<AssignmentVisitor, false, true> {
public:
  explicit AssignmentVisitor(Netlist &netlist, ast::EvalContext &evalCtx) :
    netlist(netlist), evalCtx(evalCtx) {}

  void handle(const ast::AssignmentExpression &expr) {
    // Collect variable references on the left-hand side of the assignment.
    std::vector<NetlistNode*> visitListLHS, visitListRHS;
    {
      VariableReferenceVisitor visitor(netlist, visitListLHS, evalCtx);
      expr.left().visit(visitor);
    }
    // Collect variable references on the right-hand side of the assignment.
    {
      VariableReferenceVisitor visitor(netlist, visitListRHS, evalCtx);
      expr.right().visit(visitor);
    }
    // Add edge from LHS variable refrence to variable declaration.
    for (auto *leftNode : visitListLHS) {
      std::string pathBuffer;
      leftNode->symbol.getHierarchicalPath(pathBuffer);
      //auto var = evalCtx.compilation.getRoot().lookupName(pathBuffer);
      auto *variableNode = netlist.lookupVariable(pathBuffer);
      netlist.addEdge(*leftNode, *variableNode);
      std::cout << fmt::format("Edge {} to decl {}\n", leftNode->getName(), variableNode->getName());
    }
    // Add edge from RHS variable references to variable declaration.
    for (auto *rightNode : visitListRHS) {
      std::string pathBuffer;
      rightNode->symbol.getHierarchicalPath(pathBuffer);
      //auto var = evalCtx.compilation.getRoot().lookupName(pathBuffer);
      auto *variableNode = netlist.lookupVariable(pathBuffer);
      netlist.addEdge(*variableNode, *rightNode);
      std::cout << fmt::format("Edge decl {} to {}\n", variableNode->getName(), rightNode->getName());
    }
    // Add edges form RHS expression terms to LHS expression terms.
    for (auto *leftNode : visitListLHS) {
      for (auto *rightNode : visitListRHS) {
        netlist.addEdge(*rightNode, *leftNode);
        std::cout << fmt::format("Edge {} to {}\n", leftNode->getName(), rightNode->getName());
      }
    }
  }

private:
  Netlist &netlist;
  ast::EvalContext &evalCtx;
};

/// An AST visitor for proceural blocks that performs loop unrolling.
class ProceduralBlockVisitor : public ast::ASTVisitor<ProceduralBlockVisitor, true, false> {
public:
  bool anyErrors = false;

  explicit ProceduralBlockVisitor(ast::Compilation &compilation, Netlist &netlist) :
    netlist(netlist), evalCtx(compilation) {
    evalCtx.pushEmptyFrame();
  }

  void handle(const ast::ForLoopStatement& loop) {

    // Conditions this loop cannot be unrolled.
    if (loop.loopVars.empty() || !loop.stopExpr || loop.steps.empty() || anyErrors) {
      loop.body.visit(*this);
      return;
    }

    // Attempt to unroll the loop. If we are unable to collect constant values
    // for all loop variables across all iterations, we won't unroll at all.
    auto handleFail = [&] {
      for (auto var : loop.loopVars) {
        evalCtx.deleteLocal(var);
      }
      loop.body.visit(*this);
    };

    // Create a list of the initialised loop variables.
    SmallVector<ConstantValue*> localPtrs;
    for (auto var : loop.loopVars) {
      auto init = var->getInitializer();
      if (!init) {
        handleFail();
        return;
      }

      auto cv = init->eval(evalCtx);
      if (!cv) {
        handleFail();
        return;
      }

      localPtrs.push_back(evalCtx.createLocal(var, std::move(cv)));
    }

    // Create a list of all the loop variable values across all iterations.
    SmallVector<ConstantValue, 16> values;
    while (true) {
      auto cv = step() ? loop.stopExpr->eval(evalCtx) : ConstantValue();
      if (!cv) {
        handleFail();
        return;
      }

      if (!cv.isTrue()) {
        break;
      }

      for (auto local : localPtrs) {
        values.emplace_back(*local);
      }

      for (auto step : loop.steps) {
        if (!step->eval(evalCtx)) {
          handleFail();
          return;
        }
      }
    }

    // We have all the loop iteration values. Go back through
    // and visit the loop body for each iteration.
    for (size_t i = 0; i < values.size();) {
      for (auto local : localPtrs) {
        *local = std::move(values[i++]);
      }

      loop.body.visit(*this);
      if (anyErrors)
        return;
    }
  }

  void handle(const ast::ConditionalStatement& stmt) {
    // Evaluate the condition; if not constant visit both sides,
    // otherwise visit only the side that matches the condition.
    auto fallback = [&] {
      stmt.ifTrue.visit(*this);
      if (stmt.ifFalse)
        stmt.ifFalse->visit(*this);
    };

    for (auto& cond : stmt.conditions) {
      if (cond.pattern || !step()) {
        fallback();
        return;
      }

      auto result = cond.expr->eval(evalCtx);
      if (!result) {
        fallback();
        return;
      }

      if (!result.isTrue()) {
        if (stmt.ifFalse)
          stmt.ifFalse->visit(*this);
        return;
      }
    }

    stmt.ifTrue.visit(*this);
  }

  void handle(const ast::ExpressionStatement& stmt) {
    step();
    AssignmentVisitor visitor(netlist, evalCtx);
    stmt.visit(visitor);
  }

private:
  bool step() {
    if (anyErrors || !evalCtx.step(SourceLocation::NoLocation)) {
      anyErrors = true;
      return false;
    }
    return true;
  }

  Netlist &netlist;
  ast::EvalContext evalCtx;
};

/// A base visitor that traverses the AST and builds a netlist representation.
class NetlistVisitor : public ast::ASTVisitor<NetlistVisitor, true, false> {
public:
  explicit NetlistVisitor(ast::Compilation &compilation, Netlist &netlist) :
    compilation(compilation), netlist(netlist) {}

  /// Connect ports to their corresponding variables.
  void connectInstancePorts() {
    for (auto *port : portsToConnect) {
      if (auto *internalSymbol = port->symbol.as<ast::PortSymbol>().internalSymbol) {
        std::string pathBuffer;
        internalSymbol->getHierarchicalPath(pathBuffer);
        auto *variableNode = netlist.lookupVariable(pathBuffer);
        switch (port->symbol.as<ast::PortSymbol>().direction) {
          case ast::ArgumentDirection::In:
            netlist.addEdge(*port, *variableNode);
            break;
          case ast::ArgumentDirection::Out:
            netlist.addEdge(*variableNode, *port);
            break;
          case ast::ArgumentDirection::InOut:
            netlist.addEdge(*port, *variableNode);
            netlist.addEdge(*variableNode, *port);
            break;
          case ast::ArgumentDirection::Ref:
            break;
        }
      }
    }
    portsToConnect.clear();
  }

  /// Variable declaration.
  void handle(const ast::VariableSymbol &symbol) {
    netlist.addVariableDeclaration(symbol);
  }

  /// Net declaration.
  void handle(const ast::NetSymbol &symbol) {
    netlist.addVariableDeclaration(symbol);
  }

  /// Port declaration.
  void handle(const ast::PortSymbol &symbol) {
    auto &portNode = netlist.addPortDeclaration(symbol);
    // Save this to connect it to the corresponding internal variable later.
    portsToConnect.push_back(&portNode);
  }

  /// Procedural block.
  void handle(const ast::ProceduralBlockSymbol &symbol) {
    ProceduralBlockVisitor visitor(compilation, netlist);
    symbol.visit(visitor);
  }

  /// Instance body.
  void handle(const ast::InstanceBodySymbol &symbol) {
    for (auto &member : symbol.members()) {
      member.visit(*this);
    }
    // Peform the port-variable hookups.
    connectInstancePorts();
  }

  /// Continuous assignment statement.
  void handle(const ast::ContinuousAssignSymbol &symbol) {
    ast::EvalContext evalCtx(compilation);
    AssignmentVisitor visitor(netlist, evalCtx);
    symbol.visit(visitor);
  }

  //void handle(const InstanceSymbol &symbol) {
  //  //std::cout << "InstanceSymbol " << symbol.name << "\n";
  //  for (auto *portConnection : symbol.getPortConnections()) {
  //    //std::cout << "Port " << portConnection->port.name << " connects to:\n";
  //    //if (portConnection->getExpression()) {
  //      //VariableReferenceVisitor visitor(netlist, evalCtx);
  //      //portConnection->getExpression()->visit(visitor);
  //    //}
  //  }
  //  symbol.body.visit(*this);
  //}

private:
  ast::Compilation &compilation;
  Netlist &netlist;
  std::vector<const NetlistPortDeclaration*> portsToConnect;
};

} // End namespace slang.

