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

enum class NodeKind {
  None = 0,
  PortDeclaration,
  VariableDeclaration,
  VariableReference
};

enum class VariableSelectorKind {
  ElementSelect,
  RangeSelect,
  MemberAccess
};

struct VariableSelectorBase {
  VariableSelectorKind kind;
  explicit VariableSelectorBase(VariableSelectorKind kind) : kind(kind) {}
  virtual ~VariableSelectorBase() = default;
  virtual std::string toString() const = 0;
};

/// A variable selector representing an element selector.
struct VariableElementSelect : public VariableSelectorBase {
  ConstantValue index;
  VariableElementSelect(ConstantValue index) :
    VariableSelectorBase(VariableSelectorKind::ElementSelect), index(std::move(index)) {}
  std::string toString() const override {
    return fmt::format("[%s]", index.toString());
  }
};

/// A variable selector representing a range selector.
struct VariableRangeSelect : public VariableSelectorBase {
  ConstantValue leftIndex, rightIndex;
  VariableRangeSelect(ConstantValue leftIndex, ConstantValue rightIndex) :
    VariableSelectorBase(VariableSelectorKind::RangeSelect),
    leftIndex(std::move(leftIndex)), rightIndex(std::move(rightIndex)) {}
  std::string toString() const override {
    return fmt::format("[%s:%s]", leftIndex.toString(), rightIndex.toString());
  }
};

/// A variable selector representing member access of a structure.
struct VariableMemberAccess : public VariableSelectorBase {
  std::string_view name;
  VariableMemberAccess(std::string_view name) :
    VariableSelectorBase(VariableSelectorKind::MemberAccess), name(name) {}
  std::string toString() const override {
    return fmt::format(".%s", name);
  }
};

/// A class representing a node in the netlist, corresponding to the appearance
/// of a variable symbol, with zero or more selectors applied.
class NetlistNode : public Node<NetlistNode, NetlistEdge> {
public:
  NetlistNode(NodeKind kind, const Symbol &symbol) :
    ID(++nextID), kind(kind), symbol(symbol) {};
   ~NetlistNode() override = default;

  template<typename T>
  T& as() {
    assert(T::isKind(kind));
    return *(dynamic_cast<T*>(this));
  }

  template<typename T>
  const T& as() const {
    assert(T::isKind(kind));
    return const_cast<T&>(this->as<T>());
  }

  std::string_view getName() const { return symbol.name; }
  virtual std::string toString() const = 0;

public:
  size_t ID;
  NodeKind kind;
  const Symbol &symbol;

private:
  static size_t nextID;
  std::vector<std::unique_ptr<VariableSelectorBase>> selectors;
};

size_t NetlistNode::nextID = 0;

/// A class representing a dependency between two variables in the netlist.
class NetlistEdge : public DirectedEdge<NetlistNode, NetlistEdge> {
public:
  NetlistEdge(NetlistNode &targetNode) : DirectedEdge(targetNode) {}
};

/// A class representing a port declaration.
class NetlistPortDeclaration : public NetlistNode {
public:
  NetlistPortDeclaration(const Symbol &symbol) :
    NetlistNode(NodeKind::PortDeclaration, symbol) {}

  static bool isKind(NodeKind otherKind) {
    return otherKind == NodeKind::PortDeclaration;
  }

  std::string toString() const override {
    return fmt::format("port {}", symbol.name);
  }

public:
  std::string hierarchicalPath;
};

/// A class representing a variable declaration.
class NetlistVariableDeclaration : public NetlistNode {
public:
  NetlistVariableDeclaration(const Symbol &symbol) :
    NetlistNode(NodeKind::VariableDeclaration, symbol) {}

  static bool isKind(NodeKind otherKind) {
    return otherKind == NodeKind::VariableDeclaration;
  }

  std::string toString() const override {
    return fmt::format("var {}", symbol.name);
  }

public:
  std::string hierarchicalPath;
};

/// A class representing a variable reference.
class NetlistVariableReference : public NetlistNode {
public:
  NetlistVariableReference(const Symbol &symbol) :
    NetlistNode(NodeKind::VariableReference, symbol) {}

  void addElementSelect(const ConstantValue &index) {
    selectors.emplace_back(std::make_unique<VariableElementSelect>(index));
  }
  void addRangeSelect(const ConstantValue &leftIndex, const ConstantValue &rightIndex) {
    selectors.emplace_back(std::make_unique<VariableRangeSelect>(leftIndex, rightIndex));
  }
  void addMemberAccess(std::string_view name) {
    selectors.emplace_back(std::make_unique<VariableMemberAccess>(name));
  }

  static bool isKind(NodeKind otherKind) {
    return otherKind == NodeKind::VariableReference;
  }

  std::string toString() const override {
    std::string buffer;
    for (auto &selector : selectors) {
      buffer += selector->toString();
    }
    return fmt::format("{}{}", symbol.name, buffer);
  }

private:
  std::vector<std::unique_ptr<VariableSelectorBase>> selectors;
};

/// A class representing the design netlist.
class Netlist : public DirectedGraph<NetlistNode, NetlistEdge> {
public:
  Netlist() : DirectedGraph() {}

  /// Add a port declaration node to the netlist.
  NetlistPortDeclaration &addPortDeclaration(const Symbol &symbol) {
    std::cout << "Add port decl " << symbol.name << "\n";
    auto nodePtr = std::make_unique<NetlistPortDeclaration>(symbol);
    auto &node = nodePtr->as<NetlistPortDeclaration>();
    symbol.getHierarchicalPath(node.hierarchicalPath);
    assert(lookupPort(nodePtr->hierarchicalPath) == nullptr && "Port declaration already exists");
    nodes.push_back(std::move(nodePtr));
    return node;
  }

  /// Add a variable declaration node to the netlist.
  NetlistVariableDeclaration &addVariableDeclaration(const Symbol &symbol) {
    std::cout << "Add var decl " << symbol.name << "\n";
    auto nodePtr = std::make_unique<NetlistVariableDeclaration>(symbol);
    auto &node = nodePtr->as<NetlistVariableDeclaration>();
    symbol.getHierarchicalPath(node.hierarchicalPath);
    assert(lookupVariable(nodePtr->hierarchicalPath) == nullptr && "Variable declaration already exists");
    nodes.push_back(std::move(nodePtr));
    return node;
  }

  /// Add a variable reference node to the netlist.
  NetlistVariableReference &addVariableReference(const Symbol &symbol) {
    std::cout << "Add var ref " << symbol.name << "\n";
    auto nodePtr = std::make_unique<NetlistVariableReference>(symbol);
    auto &node = nodePtr->as<NetlistVariableReference>();
    nodes.push_back(std::move(nodePtr));
    return node;
  }

  /// Find a variable declaration node in the netlist by hierarchical path.
  NetlistNode *lookupVariable(const std::string &hierarchicalPath) {
    auto compareNode = [&hierarchicalPath](const std::unique_ptr<NetlistNode> &node) {
                          return node->kind == NodeKind::VariableDeclaration &&
                                 node->as<NetlistVariableDeclaration>().hierarchicalPath == hierarchicalPath;
                       };
    auto it = std::find_if(begin(), end(), compareNode);
    return it != end() ? it->get() : nullptr;
  }

  /// Find a port declaration node in the netlist by hierarchical path.
  NetlistNode *lookupPort(const std::string &hierarchicalPath) {
    auto compareNode = [&hierarchicalPath](const std::unique_ptr<NetlistNode> &node) {
                          return node->kind == NodeKind::PortDeclaration &&
                                 node->as<NetlistPortDeclaration>().hierarchicalPath == hierarchicalPath;
                       };
    auto it = std::find_if(begin(), end(), compareNode);
    return it != end() ? it->get() : nullptr;
  }
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
    auto &node = netlist.addVariableReference(expr.symbol);
    visitList.push_back(&node);
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
  EvalContext &evalCtx;
};

/// An AST visitor for proceural blocks that performs loop unrolling.
class ProceduralBlockVisitor : public ASTVisitor<ProceduralBlockVisitor, true, false> {
public:
  bool anyErrors = false;

  explicit ProceduralBlockVisitor(Compilation &compilation, Netlist &netlist) :
    netlist(netlist), evalCtx(compilation) {
    evalCtx.pushEmptyFrame();
  }

  void handle(const ForLoopStatement& loop) {

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

/// A base visitor that traverses the AST and builds a netlist representation.
class NetlistVisitor : public ASTVisitor<NetlistVisitor, true, false> {
public:
  explicit NetlistVisitor(Compilation &compilation, Netlist &netlist) :
    compilation(compilation), netlist(netlist) {}

  /// Connect ports to their corresponding variables.
  void connectInstancePorts() {
    for (auto *port : portsToConnect) {
      if (auto *internalSymbol = port->symbol.as<PortSymbol>().internalSymbol) {
        std::string pathBuffer;
        internalSymbol->getHierarchicalPath(pathBuffer);
        auto *variableNode = netlist.lookupVariable(pathBuffer);
        switch (port->symbol.as<PortSymbol>().direction) {
          case ArgumentDirection::In:
            netlist.addEdge(*port, *variableNode);
            break;
          case ArgumentDirection::Out:
            netlist.addEdge(*variableNode, *port);
            break;
          case ArgumentDirection::InOut:
            netlist.addEdge(*port, *variableNode);
            netlist.addEdge(*variableNode, *port);
            break;
          case ArgumentDirection::Ref:
            break;
        }
      }
    }
    portsToConnect.clear();
  }

  /// Variable declaration.
  void handle(const VariableSymbol &symbol) {
    netlist.addVariableDeclaration(symbol);
  }

  /// Net declaration.
  void handle(const NetSymbol &symbol) {
    netlist.addVariableDeclaration(symbol);
  }

  /// Port declaration.
  void handle(const PortSymbol &symbol) {
    auto &portNode = netlist.addPortDeclaration(symbol);
    // Save this to connect it to the corresponding internal variable later.
    portsToConnect.push_back(&portNode);
  }

  /// Instance body.
  void handle(const InstanceBodySymbol &symbol) {
    for (auto &member : symbol.members()) {
      member.visit(*this);
    }
    // Peform the port-variable hookups.
    connectInstancePorts();
  }

  /// Continuous assignment statement.
  void handle(const ContinuousAssignSymbol &symbol) {
    EvalContext evalCtx(compilation);
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
  Compilation &compilation;
  Netlist &netlist;
  std::vector<const NetlistPortDeclaration*> portsToConnect;
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
    buffer.format("  N{} [label=\"{}\",shape=circle]\n", node->ID, node->toString());
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
    NetlistVisitor visitor(*compilation, netlist);
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
