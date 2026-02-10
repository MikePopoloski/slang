//------------------------------------------------------------------------------
// AnalysisBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/analysis/AbstractFlowAnalysis.h"
#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/AnalysisOptions.h"
#include "slang/analysis/ValueDriver.h"
#include "slang/ast/LSPUtilities.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/text/FormatBuffer.h"
#include "slang/text/SourceManager.h"

using namespace slang::analysis;

struct PyFlowState {
    py::object userData;
    bool reachable = true;
    PyFlowState() : userData(py::none()) {}
    PyFlowState(py::object ud, bool r = true) : userData(std::move(ud)), reachable(r) {}
};

class PyFlowAnalysis : public AbstractFlowAnalysis<PyFlowAnalysis, PyFlowState> {
public:
    using Base = AbstractFlowAnalysis<PyFlowAnalysis, PyFlowState>;
    friend Base;

    // Callbacks for expression/statement handling
    py::object onAssignment;       // (AssignmentExpression) -> None
    py::object onVariableRef;      // (NamedValueExpression) -> None
    py::object onCallExpression;   // (CallExpression) -> None
    py::object onConditionalBegin; // (ConditionalStatement) -> None
    py::object onCaseBegin;        // (CaseStatement) -> None
    py::object onLoopBegin;        // (Statement) -> None (any loop statement)

    // State management callbacks
    py::object onBranchMerge;  // (state1: object, state2: object) -> object (merged state)
    py::object onStateCopy;    // (state: object) -> object (copied state)
    py::object createTopState; // () -> object (initial state)

    PyFlowAnalysis(const Symbol& symbol, AnalysisOptions options = {}) : Base(symbol, options) {}

    using Base::run;

    py::object getCurrentState() const { return getState().userData; }

    void setCurrentState(py::object state) { getState().userData = std::move(state); }

    bool isBad() const { return bad; }

    EvalContext& getEvalCtx() const { return getEvalContext(); }

protected:
    void handle(const AssignmentExpression& expr) {
        if (onAssignment && !onAssignment.is_none())
            onAssignment(&expr);
        visitExpr(expr);
    }

    void handle(const NamedValueExpression& expr) {
        if (onVariableRef && !onVariableRef.is_none())
            onVariableRef(&expr);
        visitExpr(expr);
    }

    void handle(const CallExpression& expr) {
        if (onCallExpression && !onCallExpression.is_none())
            onCallExpression(&expr);
        visitExpr(expr);
    }

    void handle(const ConditionalStatement& stmt) {
        if (onConditionalBegin && !onConditionalBegin.is_none())
            onConditionalBegin(&stmt);
        visitStmt(stmt);
    }

    void handle(const CaseStatement& stmt) {
        if (onCaseBegin && !onCaseBegin.is_none())
            onCaseBegin(&stmt);
        visitStmt(stmt);
    }

    void handle(const ForLoopStatement& stmt) {
        if (onLoopBegin && !onLoopBegin.is_none())
            onLoopBegin(&stmt);
        visitStmt(stmt);
    }

    void handle(const WhileLoopStatement& stmt) {
        if (onLoopBegin && !onLoopBegin.is_none())
            onLoopBegin(&stmt);
        visitStmt(stmt);
    }

    void handle(const DoWhileLoopStatement& stmt) {
        if (onLoopBegin && !onLoopBegin.is_none())
            onLoopBegin(&stmt);
        visitStmt(stmt);
    }

    void handle(const ForeverLoopStatement& stmt) {
        if (onLoopBegin && !onLoopBegin.is_none())
            onLoopBegin(&stmt);
        visitStmt(stmt);
    }

    void handle(const ForeachLoopStatement& stmt) {
        if (onLoopBegin && !onLoopBegin.is_none())
            onLoopBegin(&stmt);
        visitStmt(stmt);
    }

    void handle(const RepeatLoopStatement& stmt) {
        if (onLoopBegin && !onLoopBegin.is_none())
            onLoopBegin(&stmt);
        visitStmt(stmt);
    }

    // state - required by AbstractFlowAnalysis
    PyFlowState topState() {
        if (createTopState && !createTopState.is_none())
            return PyFlowState(createTopState());
        return PyFlowState();
    }

    PyFlowState copyState(const PyFlowState& source) {
        if (onStateCopy && !onStateCopy.is_none())
            return PyFlowState(onStateCopy(source.userData), source.reachable);
        // default is to just copy the Python object reference
        return PyFlowState(source.userData, source.reachable);
    }

    void joinState(PyFlowState& result, const PyFlowState& other) {
        if (result.reachable == other.reachable) {
            if (onBranchMerge && !onBranchMerge.is_none()) {
                result.userData = onBranchMerge(result.userData, other.userData);
            }
        }
        else if (!result.reachable) {
            result = copyState(other);
        }
    }

    void meetState(PyFlowState& result, const PyFlowState& other) {
        if (!other.reachable) {
            result.reachable = false;
            return;
        }
        joinState(result, other);
    }

    PyFlowState unreachableState() {
        PyFlowState state;
        state.reachable = false;
        return state;
    }
};

void registerAnalysis(py::module_& m, py::module_& ast) {
    py::native_enum<DriverKind>(m, "DriverKind", "enum.Enum")
        .value("Procedural", DriverKind::Procedural)
        .value("Continuous", DriverKind::Continuous)
        .finalize();

    py::native_enum<AnalysisFlags>(m, "AnalysisFlags", "enum.Flag")
        .value("None", AnalysisFlags::None)
        .value("CheckUnused", AnalysisFlags::CheckUnused)
        .value("FullCaseUniquePriority", AnalysisFlags::FullCaseUniquePriority)
        .value("FullCaseFourState", AnalysisFlags::FullCaseFourState)
        .value("AllowMultiDrivenLocals", AnalysisFlags::AllowMultiDrivenLocals)
        .value("AllowDupInitialDrivers", AnalysisFlags::AllowDupInitialDrivers)
        .finalize();

    py::classh<AnalysisOptions>(m, "AnalysisOptions")
        .def(py::init<>())
        .def_readwrite("flags", &AnalysisOptions::flags)
        .def_readwrite("numThreads", &AnalysisOptions::numThreads)
        .def_readwrite("maxCaseAnalysisSteps", &AnalysisOptions::maxCaseAnalysisSteps)
        .def_readwrite("maxLoopAnalysisSteps", &AnalysisOptions::maxLoopAnalysisSteps);

    py::classh<AnalyzedScope>(m, "AnalyzedScope")
        .def_property_readonly("scope", [](const AnalyzedScope& s) { return &s.scope; })
        .def_readonly("procedures", &AnalyzedScope::procedures);

    py::classh<ValueDriver>(m, "ValueDriver")
        .def_readonly("lsp", &ValueDriver::lsp)
        .def_readonly("containingSymbol", &ValueDriver::containingSymbol)
        .def_readonly("flags", &ValueDriver::flags)
        .def_readonly("kind", &ValueDriver::kind)
        .def_readonly("source", &ValueDriver::source)
        .def_property_readonly("sourceRange", &ValueDriver::getSourceRange)
        .def_property_readonly("overrideRange", &ValueDriver::getOverrideRange)
        .def_property_readonly("isInputPort", &ValueDriver::isInputPort)
        .def_property_readonly("isUnidirectionalPort", &ValueDriver::isUnidirectionalPort)
        .def_property_readonly("isClockVar", &ValueDriver::isClockVar)
        .def_property_readonly("isInSingleDriverProcedure",
                               &ValueDriver::isInSingleDriverProcedure);

    py::classh<AnalysisManager>(m, "AnalysisManager")
        .def(py::init<AnalysisOptions>(), "options"_a = AnalysisOptions())
        .def("addProcListener",
             py::overload_cast<std::function<void(const AnalyzedProcedure&)>>(
                 &AnalysisManager::addListener),
             "listener"_a)
        .def("addScopeListener",
             py::overload_cast<std::function<void(const AnalyzedScope&)>>(
                 &AnalysisManager::addListener),
             "listener"_a)
        .def("addAssertionListener",
             py::overload_cast<std::function<void(const AnalyzedAssertion&)>>(
                 &AnalysisManager::addListener),
             "listener"_a)
        .def("analyze", &AnalysisManager::analyze, "compilation"_a)
        .def("getDrivers", &AnalysisManager::getDrivers, "symbol"_a, byrefint)
        .def("getDiagnostics", &AnalysisManager::getDiagnostics)
        .def("getAnalyzedScope", &AnalysisManager::getAnalyzedScope, "scope"_a, byrefint)
        .def("getAnalyzedSubroutine", &AnalysisManager::getAnalyzedSubroutine, "symbol"_a, byrefint)
        .def("getAnalyzedAssertions", &AnalysisManager::getAnalyzedAssertions, "symbol"_a, byrefint)
        .def_property_readonly("options", &AnalysisManager::getOptions);

    py::classh<AnalyzedProcedure>(m, "AnalyzedProcedure")
        .def_readonly("analyzedSymbol", &AnalyzedProcedure::analyzedSymbol)
        .def_readonly("parentProcedure", &AnalyzedProcedure::parentProcedure)
        .def_property_readonly("inferredClock", &AnalyzedProcedure::getInferredClock)
        .def_property_readonly("drivers", &AnalyzedProcedure::getDrivers)
        .def_property_readonly("callExpressions", &AnalyzedProcedure::getCallExpressions);

    py::classh<AnalyzedAssertion>(m, "AnalyzedAssertion")
        .def_readonly("containingSymbol", &AnalyzedAssertion::containingSymbol)
        .def_readonly("procedure", &AnalyzedAssertion::procedure)
        .def_readonly("astNode", &AnalyzedAssertion::astNode)
        .def_property_readonly("semanticLeadingClock", &AnalyzedAssertion::getSemanticLeadingClock)
        .def_property_readonly("root", &AnalyzedAssertion::getRoot)
        .def("getClock", &AnalyzedAssertion::getClock, "expr"_a, byrefint);

    py::classh<PyFlowAnalysis>(
        m, "FlowAnalysis",
        "A flow analysis visitor that walks statements with proper control flow handling.\n\n"
        "Set callback attributes before calling run():\n"
        "- onAssignment: called for each assignment expression\n"
        "- onVariableRef: called for each variable reference (NamedValueExpression)\n"
        "- onCallExpression: called for each function/task call\n"
        "- onConditionalBegin: called when entering an if/else\n"
        "- onCaseBegin: called when entering a case statement\n"
        "- onLoopBegin: called when entering any loop statement\n"
        "- onBranchMerge: called when control flow paths merge (state1, state2) -> merged_state\n"
        "- onStateCopy: called to copy state when forking (state) -> copied_state\n"
        "- createTopState: called to create initial state () -> state")
        .def(py::init<const Symbol&, AnalysisOptions>(), "symbol"_a,
             "options"_a = AnalysisOptions(),
             "Create a flow analysis for the given symbol (procedural block, subroutine, etc.)")
        .def(
            "run", [](PyFlowAnalysis& self, const Statement& stmt) { self.run(stmt); }, "stmt"_a,
            "Run the analysis on a statement")
        .def(
            "run", [](PyFlowAnalysis& self, const Expression& expr) { self.run(expr); }, "expr"_a,
            "Run the analysis on an expression")
        .def_property("currentState", &PyFlowAnalysis::getCurrentState,
                      &PyFlowAnalysis::setCurrentState, "The current flow state's user data")
        .def_property_readonly("bad", &PyFlowAnalysis::isBad,
                               "True if the analysis detected an error")
        .def_property_readonly("evalContext", &PyFlowAnalysis::getEvalCtx, byrefint,
                               "The evaluation context for use during analysis")
        .def_readwrite("onAssignment", &PyFlowAnalysis::onAssignment,
                       "Callback for assignment expressions: (AssignmentExpression) -> None")
        .def_readwrite("onVariableRef", &PyFlowAnalysis::onVariableRef,
                       "Callback for variable references: (NamedValueExpression) -> None")
        .def_readwrite("onCallExpression", &PyFlowAnalysis::onCallExpression,
                       "Callback for function/task calls: (CallExpression) -> None")
        .def_readwrite("onConditionalBegin", &PyFlowAnalysis::onConditionalBegin,
                       "Callback when entering conditional: (ConditionalStatement) -> None")
        .def_readwrite("onCaseBegin", &PyFlowAnalysis::onCaseBegin,
                       "Callback when entering case: (CaseStatement) -> None")
        .def_readwrite("onLoopBegin", &PyFlowAnalysis::onLoopBegin,
                       "Callback when entering any loop: (Statement) -> None")
        .def_readwrite("onBranchMerge", &PyFlowAnalysis::onBranchMerge,
                       "Callback when branches merge: (state1, state2) -> merged_state")
        .def_readwrite("onStateCopy", &PyFlowAnalysis::onStateCopy,
                       "Callback to copy state: (state) -> copied_state")
        .def_readwrite("createTopState", &PyFlowAnalysis::createTopState,
                       "Callback to create initial state: () -> state");

    py::classh<LSPUtilities>(
        ast, "LSPUtilities",
        "Utility methods for working with Longest Static Prefix (LSP) expressions.\n\n"
        "An LSP expression is the longest static prefix of an expression that can be\n"
        "used to identify a particular driver of a variable. For example, in the\n"
        "expression `a.b[3].c.d[2:0]`, if all of the selects are constant, then the entire\n"
        "expression is the LSP. If instead we had `a.b[i].c.d[2:0]`, then the LSP would be\n"
        "`a.b` (the `[i]` part is not static).")
        .def_static(
            "getBounds",
            [](const Expression& lsp, EvalContext& evalContext) -> py::object {
                // Walk the LSP expression to find the root ValueSymbol
                const Expression* expr = &lsp;
                while (true) {
                    switch (expr->kind) {
                        case ExpressionKind::NamedValue:
                        case ExpressionKind::HierarchicalValue:
                            goto found;
                        case ExpressionKind::Conversion:
                            expr = &expr->as<ConversionExpression>().operand();
                            break;
                        case ExpressionKind::ElementSelect:
                            expr = &expr->as<ElementSelectExpression>().value();
                            break;
                        case ExpressionKind::RangeSelect:
                            expr = &expr->as<RangeSelectExpression>().value();
                            break;
                        case ExpressionKind::MemberAccess:
                            expr = &expr->as<MemberAccessExpression>().value();
                            break;
                        default:
                            return py::none();
                    }
                }
            found:
                const Type& rootType = expr->as<ValueExpressionBase>().symbol.getType();
                auto result = LSPUtilities::getBounds(lsp, evalContext, rootType);
                if (result) {
                    return py::make_tuple(result->first, result->second);
                }
                return py::none();
            },
            "lsp"_a, "eval_context"_a,
            "Computes bit bounds for a driver given its longest static prefix expression.\n\n"
            "Returns a tuple (lower, upper) representing the bit range, or None if bounds\n"
            "cannot be determined.")
        .def_static(
            "stringifyLSP",
            [](const Expression& expr, Compilation& compilation) -> std::string {
                ASTContext astCtx(compilation.getRoot(), LookupLocation::max);
                EvalContext evalCtx(astCtx);
                FormatBuffer buffer;
                LSPUtilities::stringifyLSP(expr, evalCtx, buffer);
                return std::string(buffer.str());
            },
            "expr"_a, "compilation"_a,
            "Converts an LSP expression to a human-friendly string representation.")
        .def_static(
            "visitLSPs",
            [](const Expression& expr, Compilation& compilation, py::function callback,
               bool isLValue) {
                ASTContext astCtx(compilation.getRoot(), LookupLocation::max);
                EvalContext evalCtx(astCtx);

                LSPUtilities::visitLSPs(
                    expr, evalCtx,
                    [&callback](const ValueSymbol& symbol, const Expression& lsp, bool isLVal) {
                        callback(&symbol, &lsp, isLVal);
                    },
                    isLValue);
            },
            "expr"_a, "compilation"_a, "callback"_a, "is_lvalue"_a = true,
            "Visits the longest static prefix expressions for all operands in the expression.\n\n"
            "The callback receives (symbol, lsp_expr, is_lvalue) for each found LSP.");
}
