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

#include "DirectedGraph.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::driver;

class VariableReferenceVisitor : public ASTVisitor<VariableReferenceVisitor, false, true> {
  EvalContext &evalCtx;
  std::vector<const Expression*> selectors;

public:
  explicit VariableReferenceVisitor(EvalContext &evalCtx) : evalCtx(evalCtx) {}

  void handle(const AssignmentExpression &expr) {
    std::cout << "AssignmentExpression non-blocking " << expr.isNonBlocking() << "\n";
    expr.left().visit(*this);
    expr.right().visit(*this);
  }

  void handle(const NamedValueExpression &expr) {
    std::cout << "NamedValueExpression " << expr.symbol.name << "\n";
    for (auto *selector : selectors) {
      if (selector->kind == ExpressionKind::ElementSelect) {
        auto index = selector->as<ElementSelectExpression>().selector().eval(evalCtx);
        std::cout << "ElementSelectExpression " << index.toString() << "\n";
      }
      else if (selector->kind == ExpressionKind::RangeSelect) {
        auto &rangeSelectExpr = selector->as<RangeSelectExpression>();
        auto leftIndex = rangeSelectExpr.left().eval(evalCtx);
        auto rightIndex = rangeSelectExpr.right().eval(evalCtx);
        std::cout << "RangeSelectExpression "
                  << leftIndex.toString() << ":"
                  << rightIndex.toString() << "\n";
      }
      else if (selector->kind == ExpressionKind::MemberAccess) {
        std::cout << "MemberAccessExpression "
                  << selector->as<MemberAccessExpression>().member.name << "\n";
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
};

class UnrollVisitor : public ASTVisitor<UnrollVisitor, true, false> {
public:
  bool anyErrors = false;

  explicit UnrollVisitor(Compilation &compilation) :
    evalCtx(compilation) {
    evalCtx.pushEmptyFrame();
  }

  void handle(const InstanceSymbol &symbol) {
    std::cout << "InstanceSymbol " << symbol.name << "\n";
    for (auto *portConnection : symbol.getPortConnections()) {
      std::cout << "Port " << portConnection->port.name << " connects to:\n";
      if (portConnection->getExpression()) {
        VariableReferenceVisitor visitor(evalCtx);
        portConnection->getExpression()->visit(visitor);
      }
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
  }

  void handle(const ForLoopStatement& loop) {
    std::cout << "Unroll ForLoopStatement\n";

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
    std::cout << "ConditionalStatement\n";
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
    std::cout << "ExpressionStatement\n";
    step();
    VariableReferenceVisitor visitor(evalCtx);
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

  EvalContext evalCtx;
};

void writeToFile(string_view fileName, string_view contents);

void printJson(Compilation& compilation, const std::string& fileName,
               const std::vector<std::string>& scopes) {
    JsonWriter writer;
    writer.setPrettyPrint(true);

    ASTSerializer serializer(compilation, writer);
    if (scopes.empty()) {
        serializer.serialize(compilation.getRoot());
    }
    else {
        for (auto& scopeName : scopes) {
            auto sym = compilation.getRoot().lookupName(scopeName);
            if (sym)
                serializer.serialize(*sym);
        }
    }

    writeToFile(fileName, writer.view());
}

template<typename Stream, typename String>
void writeToFile(Stream& os, string_view fileName, String contents) {
    os.write(contents.data(), contents.size());
    os.flush();
    if (!os)
        throw std::runtime_error(fmt::format("Unable to write AST to '{}'", fileName));
}

void writeToFile(string_view fileName, string_view contents) {
    if (fileName == "-") {
        writeToFile(std::cout, "stdout", contents);
    }
    else {
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

  UnrollVisitor visitor(*compilation);
  compilation->getRoot().visit(visitor);

  return 0;
    return 0;
}
