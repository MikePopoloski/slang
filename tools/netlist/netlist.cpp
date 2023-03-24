//------------------------------------------------------------------------------
//! @file netlist.cpp
//! @brief The slang netlist tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "fmt/color.h"
#include "fmt/format.h"
#include <unordered_set>
#include <fstream>
#include <iostream>
#include <utility>
#include <vector>

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/text/Json.h"
#include "slang/util/TimeTrace.h"
#include "slang/util/Version.h"
#include "slang/util/Util.h"
#include "slang/text/FormatBuffer.h"

#include "DirectedGraph.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::driver;

class NetlistNode;
class NetlistEdge;
using Netlist = DirectedGraph<NetlistNode, NetlistEdge>;

enum class VariableSelectorKind {
  ElementSelect,
  RangeSelect,
  MemberAccess
};

struct VariableSelectorBase {
  VariableSelectorKind kind;
  explicit VariableSelectorBase(VariableSelectorKind kind) : kind(kind) {}
};

/// A variable selector representing an element selector.
struct VariableElementSelect : public VariableSelectorBase {
  ConstantValue index;
  VariableElementSelect(ConstantValue index) :
    VariableSelectorBase(VariableSelectorKind::ElementSelect), index(std::move(index)) {}
  std::string toString() const {
    return fmt::format("[%s]", index.toString());
  }
};

/// A variable selector representing a range selector.
struct VariableRangeSelect : public VariableSelectorBase {
  ConstantValue leftIndex, rightIndex;
  VariableRangeSelect(ConstantValue leftIndex, ConstantValue rightIndex) :
    VariableSelectorBase(VariableSelectorKind::RangeSelect),
    leftIndex(std::move(leftIndex)), rightIndex(std::move(rightIndex)) {}
  std::string toString() const {
    return fmt::format("[%s:%s]", leftIndex.toString(), rightIndex.toString());
  }
};

/// A variable selector representing member access of a structure.
struct VariableMemberAccess : public VariableSelectorBase {
  std::string_view name;
  VariableMemberAccess(std::string_view name) :
    VariableSelectorBase(VariableSelectorKind::MemberAccess), name(name) {}
  std::string toString() const {
    return fmt::format(".%s", name);
  }
};

/// A class representing a node in the netlist, corresponding to the appearance
/// of a variable symbol, with zero or more selectors applied.
class NetlistNode : public Node<NetlistNode, NetlistEdge> {
public:
  NetlistNode() : ID(++nextID) {};
  void addElementSelect(const ConstantValue &index) {
    selectors.emplace_back(std::make_unique<VariableElementSelect>(index));
  }
  void addRangeSelect(const ConstantValue &leftIndex, const ConstantValue &rightIndex) {
    selectors.emplace_back(std::make_unique<VariableRangeSelect>(leftIndex, rightIndex));
  }
  void addMemberAccess(std::string_view name) {
    selectors.emplace_back(std::make_unique<VariableMemberAccess>(name));
  }
  std::string_view getName() const { return symbol->name; }

public:
  size_t ID;
  const Symbol *symbol;

private:
  static size_t nextID;
  std::vector<std::unique_ptr<VariableSelectorBase>> selectors;
};

size_t NetlistNode::nextID = 0;

class NetlistEdge : public DirectedEdge<NetlistNode, NetlistEdge> {
public:
  NetlistEdge(NetlistNode &targetNode) : DirectedEdge(targetNode) {}
};

/// An AST visitor to identify variable references with selectors in
/// expressions only.
class VariableReferenceVisitor : public ASTVisitor<VariableReferenceVisitor, false, true> {
public:
  explicit VariableReferenceVisitor(Netlist &netlist,
                                    std::vector<NetlistNode*> &visitList,
                                    EvalContext &evalCtx) :
    netlist(netlist), visitList(visitList), evalCtx(evalCtx) {}

  void handle(const NamedValueExpression &expr) {
    auto &node = netlist.addNode();
    visitList.push_back(&node);
    node.symbol = &(expr.symbol);
    for (auto *selector : selectors) {
      if (selector->kind == ExpressionKind::ElementSelect) {
        auto index = selector->as<ElementSelectExpression>().selector().eval(evalCtx);
        node.addElementSelect(index);
      }
      else if (selector->kind == ExpressionKind::RangeSelect) {
        auto &rangeSelectExpr = selector->as<RangeSelectExpression>();
        auto leftIndex = rangeSelectExpr.left().eval(evalCtx);
        auto rightIndex = rangeSelectExpr.right().eval(evalCtx);
        node.addRangeSelect(leftIndex, rightIndex);
      }
      else if (selector->kind == ExpressionKind::MemberAccess) {
        node.addMemberAccess(selector->as<MemberAccessExpression>().member.name);
      }
    }
    selectors.clear();
  }

  void handle(const ElementSelectExpression &expr) {
    selectors.push_back(&expr);
    expr.value().visit(*this);
  }

  void handle(const RangeSelectExpression &expr) {
    selectors.push_back(&expr);
    expr.value().visit(*this);
  }

  void handle(const MemberAccessExpression &expr) {
    selectors.push_back(&expr);
    expr.value().visit(*this);
  }

private:
  Netlist &netlist;
  std::vector<NetlistNode*> &visitList;
  EvalContext &evalCtx;
  std::vector<const Expression*> selectors;
};

/// An AST visitor to create dependencies between occurrances of variables
/// appearing on the left and right hand sides of assignment statements.
class AssignmentVisitor : public ASTVisitor<AssignmentVisitor, false, true> {
public:
  explicit AssignmentVisitor(Netlist &netlist, EvalContext &evalCtx) :
    netlist(netlist), evalCtx(evalCtx) {}

  void handle(const AssignmentExpression &expr) {
    std::cout << "AssignmentExpression non-blocking " << expr.isNonBlocking() << "\n";
    // Collect variable references on the left and right hand sides of the
    // assignment.
    std::vector<NetlistNode*> visitListLHS, visitListRHS;
    {
      VariableReferenceVisitor visitor(netlist, visitListLHS, evalCtx);
      expr.left().visit(visitor);
    }
    {
      VariableReferenceVisitor visitor(netlist, visitListRHS, evalCtx);
      expr.right().visit(visitor);
    }
    // Add edges RHS -> LHS...
    for (auto *leftNode : visitListLHS) {
      for (auto *rightNode : visitListRHS) {
        netlist.addEdge(*leftNode, *rightNode);
        //std::cout<<"add edge "<<rightNode->getName()<< " to " <<leftNode->getName()<<"\n";
      }
    }
  }

private:
  Netlist &netlist;
  EvalContext &evalCtx;
};

class UnrollVisitor : public ASTVisitor<UnrollVisitor, true, false> {
public:
  bool anyErrors = false;

  explicit UnrollVisitor(Compilation &compilation, Netlist &netlist) :
    netlist(netlist), evalCtx(compilation) {
    evalCtx.pushEmptyFrame();
  }

  void handle(const InstanceSymbol &symbol) {
    std::cout << "InstanceSymbol " << symbol.name << "\n";
    for (auto *portConnection : symbol.getPortConnections()) {
      std::cout << "Port " << portConnection->port.name << " connects to:\n";
      //if (portConnection->getExpression()) {
        //VariableReferenceVisitor visitor(netlist, evalCtx);
        //portConnection->getExpression()->visit(visitor);
      //}
    }
    symbol.body.visit(*this);
  }

  void handle(const InstanceBodySymbol &symbol) {
    std::cout << "InstanceBodySymbol\n";
    for (auto& member : symbol.members()) {
      member.visit(*this);
    }
  }

  void handle(const PortSymbol &symbol) {
    std::cout << "PortSymbol " << symbol.name << "\n";
    auto &node = netlist.addNode();
    node.symbol = &symbol;
  }

  void handle(const ContinuousAssignSymbol &symbol) {
    AssignmentVisitor visitor(netlist, evalCtx);
    symbol.visit(visitor);
  }

  void handle(const ForLoopStatement& loop) {
//    std::cout << "Unroll ForLoopStatement\n";

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

  void handle(const ConditionalStatement& stmt) {
//    std::cout << "ConditionalStatement\n";
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

  void handle(const ExpressionStatement& stmt) {
//    std::cout << "ExpressionStatement\n";
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
  EvalContext evalCtx;
};

void writeToFile(std::string_view fileName, std::string_view contents);

void printJson(Compilation& compilation, const std::string& fileName,
               const std::vector<std::string>& scopes) {
    JsonWriter writer;
    writer.setPrettyPrint(true);
    ASTSerializer serializer(compilation, writer);
    if (scopes.empty()) {
      serializer.serialize(compilation.getRoot());
    } else {
      for (auto& scopeName : scopes) {
        auto sym = compilation.getRoot().lookupName(scopeName);
        if (sym) {
          serializer.serialize(*sym);
        }
      }
    }
    writeToFile(fileName, writer.view());
}

void printDOT(const Netlist &netlist, const std::string &fileName) {
  slang::FormatBuffer buffer;
  buffer.append("digraph {\n");
  for (auto &node : netlist) {
    buffer.format("  N{} [label=\"{}\",shape=circle]\n", node->ID, node->getName());
  }
  for (auto &node : netlist) {
    for (auto &edge : node->getEdges()) {
      buffer.format("  N{} -> N{}\n", node->ID, edge->getTargetNode().ID);
    }
  }
  buffer.append("}\n");
  writeToFile(fileName, std::string_view(buffer.data()));
}

template<typename Stream, typename String>
void writeToFile(Stream& os, std::string_view fileName, String contents) {
  os.write(contents.data(), contents.size());
  os.flush();
  if (!os) {
    throw std::runtime_error(fmt::format("Unable to write AST to '{}'", fileName));
  }
}

void writeToFile(std::string_view fileName, std::string_view contents) {
  if (fileName == "-") {
    writeToFile(std::cout, "stdout", contents);
  } else {
    std::ofstream file{std::string(fileName)};
    writeToFile(file, fileName, contents);
  }
}

int main(int argc, char** argv) {

  driver::Driver driver;
  driver.addStandardArgs();

  std::optional<bool> showHelp;
  std::optional<bool> showVersion;
  std::optional<bool> quiet;
  driver.cmdLine.add("-h,--help", showHelp, "Display available options");
  driver.cmdLine.add("--version", showVersion, "Display version information and exit");
  driver.cmdLine.add("-q,--quiet", quiet, "Suppress non-essential output");

  std::optional<std::string> astJsonFile;
  driver.cmdLine.add("--ast-json", astJsonFile,
                     "Dump the compiled AST in JSON format to the specified file, or '-' for stdout", "<file>",
                     /* isFileName */ true);

  std::vector<std::string> astJsonScopes;
  driver.cmdLine.add("--ast-json-scope", astJsonScopes,
                     "When dumping AST to JSON, include only the scopes specified by the "
                     "given hierarchical paths",
                     "<path>");

  std::optional<std::string> netlistDotFile;
  driver.cmdLine.add("--netlist-dot", netlistDotFile,
                     "Dump the netlist in DOT format to the specified file, or '-' for stdout", "<file>",
                     /* isFileName */ true);

  if (!driver.parseCommandLine(argc, argv)) {
    return 1;
  }

  if (showHelp == true) {
    printf("%s\n", driver.cmdLine.getHelpText("slang SystemVerilog compiler").c_str());
    return 0;
  }

  if (showVersion == true) {
    printf("slang version %d.%d.%d+%s\n", VersionInfo::getMajor(),
        VersionInfo::getMinor(), VersionInfo::getPatch(),
        std::string(VersionInfo::getHash()).c_str());
    return 0;
  }

  if (!driver.processOptions()) {
    return 2;
  }

  try {

    bool ok = driver.parseAllSources();

    auto compilation = driver.createCompilation();
    ok &= driver.reportCompilation(*compilation, quiet == true);

    if (!ok) {
      return ok;
    }

    if (astJsonFile) {
      printJson(*compilation, *astJsonFile, astJsonScopes);
      return 0;
    }

    // Create the netlist by traversing the AST.
    Netlist netlist;
    UnrollVisitor visitor(*compilation, netlist);
    compilation->getRoot().visit(visitor);
    std::cout << fmt::format("Netlist has {} nodes and {} edges\n",
                             netlist.numNodes(), netlist.numEdges());

    if (netlistDotFile) {
      printDOT(netlist, *netlistDotFile);
      return 0;
    }

  } catch (const std::exception& e) {
    OS::printE(fmt::format("{}\n", e.what()));
    return 3;
  }

  return 0;
}
