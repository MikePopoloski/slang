//------------------------------------------------------------------------------
// AnalysisBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/analysis/AbstractFlowAnalysis.h"
#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/AnalysisOptions.h"
#include "slang/analysis/AnalyzedProcedure.h"
#include "slang/analysis/ValueDriver.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/text/SourceManager.h"

using namespace slang::analysis;

struct PyFlowState {
    nb::object userData;
    bool reachable = true;
    PyFlowState() : userData(nb::none()) {}
    PyFlowState(nb::object ud, bool r = true) : userData(std::move(ud)), reachable(r) {}
};

class PyFlowAnalysis : public AbstractFlowAnalysis<PyFlowAnalysis, PyFlowState> {
public:
    using Base = AbstractFlowAnalysis<PyFlowAnalysis, PyFlowState>;
    friend Base;

    // Callbacks for expression/statement handling
    nb::object onAssignment;       // (AssignmentExpression) -> None
    nb::object onVariableRef;      // (NamedValueExpression) -> None
    nb::object onCallExpression;   // (CallExpression) -> None
    nb::object onConditionalBegin; // (ConditionalStatement) -> None
    nb::object onCaseBegin;        // (CaseStatement) -> None
    nb::object onLoopBegin;        // (Statement) -> None (any loop statement)

    // State management callbacks
    nb::object onBranchMerge;  // (state1: object, state2: object) -> object
                               // (merged state)
    nb::object onStateCopy;    // (state: object) -> object (copied state)
    nb::object createTopState; // () -> object (initial state)

    PyFlowAnalysis(const Symbol& symbol, AnalysisOptions options = {}) : Base(symbol, options) {}

    using Base::run;

    nb::object getCurrentState() const { return getState().userData; }

    void setCurrentState(nb::object state) { getState().userData = std::move(state); }

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

struct PyAnalysisManager {
    AnalysisManager manager;
    std::vector<nb::object> listeners;

    explicit PyAnalysisManager(AnalysisOptions options) : manager(std::move(options)) {}
};

static int py_analysis_manager_traverse(PyObject* self, visitproc visit, void* arg) {
    auto* p = nb::inst_ptr<PyAnalysisManager>(self);
    if (p) {
        for (auto& cb : p->listeners) {
            Py_VISIT(cb.ptr());
        }
    }
    return 0;
}

static int py_analysis_manager_clear(PyObject* self) {
    auto* p = nb::inst_ptr<PyAnalysisManager>(self);
    if (p) {
        p->listeners.clear();
    }
    return 0;
}

static PyType_Slot py_analysis_manager_slots[] = {{Py_tp_traverse,
                                                   (void*)py_analysis_manager_traverse},
                                                  {Py_tp_clear, (void*)py_analysis_manager_clear},
                                                  {0, nullptr}};

void registerAnalysis(nb::module_& m, nb::module_& ast) {
    nb::enum_<DriverKind>(m, "DriverKind")
        .value("Procedural", DriverKind::Procedural)
        .value("Continuous", DriverKind::Continuous);

    nb::enum_<DriverSource>(m, "DriverSource")
        .value("Initial", DriverSource::Initial)
        .value("Final", DriverSource::Final)
        .value("Always", DriverSource::Always)
        .value("AlwaysComb", DriverSource::AlwaysComb)
        .value("AlwaysLatch", DriverSource::AlwaysLatch)
        .value("AlwaysFF", DriverSource::AlwaysFF)
        .value("Subroutine", DriverSource::Subroutine)
        .value("Other", DriverSource::Other);

    nb::enum_<DriverFlags>(m, "DriverFlags", nb::is_arithmetic())
        .value("None", DriverFlags::None)
        .value("InputPort", DriverFlags::InputPort)
        .value("OutputPort", DriverFlags::OutputPort)
        .value("ClockVar", DriverFlags::ClockVar)
        .value("Initializer", DriverFlags::Initializer)
        .value("FromSideEffect", DriverFlags::FromSideEffect)
        .value("HasOverrideRange", DriverFlags::HasOverrideRange)
        .value("ViaIndirectPort", DriverFlags::ViaIndirectPort);

    nb::enum_<AnalysisFlags>(m, "AnalysisFlags", nb::is_arithmetic())
        .value("None", AnalysisFlags::None)
        .value("CheckUnused", AnalysisFlags::CheckUnused)
        .value("FullCaseUniquePriority", AnalysisFlags::FullCaseUniquePriority)
        .value("FullCaseFourState", AnalysisFlags::FullCaseFourState)
        .value("AllowMultiDrivenLocals", AnalysisFlags::AllowMultiDrivenLocals)
        .value("AllowDupInitialDrivers", AnalysisFlags::AllowDupInitialDrivers)
        .value("CheckShadow", AnalysisFlags::CheckShadow)
        .value("InlineContAssignFunctionReads", AnalysisFlags::InlineContAssignFunctionReads)
        .value("AlwaysStarUsesLSPs", AnalysisFlags::AlwaysStarUsesLSPs)
        .value("ContAssignUsesLSPs", AnalysisFlags::ContAssignUsesLSPs);

    nb::class_<AnalysisOptions>(m, "AnalysisOptions")
        .def(nb::init<>())
        .def_rw("flags", &AnalysisOptions::flags)
        .def_rw("maxCaseAnalysisSteps", &AnalysisOptions::maxCaseAnalysisSteps)
        .def_rw("maxLoopAnalysisSteps", &AnalysisOptions::maxLoopAnalysisSteps);

    nb::class_<AnalyzedScope>(m, "AnalyzedScope")
        .def_prop_ro("scope", [](const AnalyzedScope& s) { return &s.scope; })
        .def_ro("procedures", &AnalyzedScope::procedures);

    nb::class_<ValueDriver>(m, "ValueDriver")
        .def_ro("path", &ValueDriver::path)
        .def_ro("containingSymbol", &ValueDriver::containingSymbol)
        .def_ro("flags", &ValueDriver::flags)
        .def_ro("kind", &ValueDriver::kind)
        .def_ro("source", &ValueDriver::source)
        .def_prop_ro("symbol", &ValueDriver::getSymbol)
        .def_prop_ro("bounds", &ValueDriver::getBounds)
        .def_prop_ro("sourceRange", &ValueDriver::getSourceRange)
        .def_prop_ro("overrideRange", &ValueDriver::getOverrideRange)
        .def_prop_ro("isInputPort", &ValueDriver::isInputPort)
        .def_prop_ro("isUnidirectionalPort", &ValueDriver::isUnidirectionalPort)
        .def_prop_ro("isClockVar", &ValueDriver::isClockVar)
        .def_prop_ro("isInSingleDriverProcedure", &ValueDriver::isInSingleDriverProcedure);

    nb::class_<PyAnalysisManager>(m, "AnalysisManager", nb::type_slots(py_analysis_manager_slots))
        .def(
            "__init__",
            [](PyAnalysisManager* self, AnalysisOptions options) {
                new (self) PyAnalysisManager(std::move(options));
            },
            "options"_a = AnalysisOptions())
        .def(
            "addProcListener",
            [](PyAnalysisManager& self, nb::object cb) {
                size_t idx = self.listeners.size();
                self.listeners.push_back(cb);
                self.manager.addListener([&self, idx](const AnalyzedProcedure& proc) {
                    nb::handle fn = self.listeners[idx];
                    fn(nb::cast(&proc, nb::rv_policy::reference_internal, nb::find(&self)));
                });
            },
            "listener"_a)
        .def(
            "addScopeListener",
            [](PyAnalysisManager& self, nb::object cb) {
                size_t idx = self.listeners.size();
                self.listeners.push_back(cb);
                self.manager.addListener([&self, idx](const AnalyzedScope& scope) {
                    nb::handle fn = self.listeners[idx];
                    fn(nb::cast(&scope, nb::rv_policy::reference_internal, nb::find(&self)));
                });
            },
            "listener"_a)
        .def(
            "addAssertionListener",
            [](PyAnalysisManager& self, nb::object cb) {
                size_t idx = self.listeners.size();
                self.listeners.push_back(cb);
                self.manager.addListener([&self, idx](const AnalyzedAssertion& aa) {
                    nb::handle fn = self.listeners[idx];
                    fn(nb::cast(&aa, nb::rv_policy::reference_internal, nb::find(&self)));
                });
            },
            "listener"_a)
        .def(
            "analyze",
            [](PyAnalysisManager& self, const ast::Compilation& compilation) {
                self.manager.analyze(compilation);
            },
            "compilation"_a, nb::keep_alive<1, 2>())
        .def(
            "getDrivers",
            [](const PyAnalysisManager& self, const ast::ValueSymbol& symbol) {
                return self.manager.getDrivers(symbol);
            },
            "symbol"_a, byrefint)
        .def(
            "getDiagnostics", [](PyAnalysisManager& self) { return self.manager.getDiagnostics(); },
            byrefint)
        .def(
            "getAnalyzedScope",
            [](const PyAnalysisManager& self, const ast::Scope& scope) {
                return self.manager.getAnalyzedScope(scope);
            },
            "scope"_a, byrefint)
        .def(
            "getAnalyzedSubroutine",
            [](const PyAnalysisManager& self, const ast::SubroutineSymbol& symbol) {
                return self.manager.getAnalyzedSubroutine(symbol);
            },
            "symbol"_a, byrefint)
        .def(
            "getAnalyzedAssertions",
            [](const PyAnalysisManager& self, const ast::Symbol& symbol) {
                return self.manager.getAnalyzedAssertions(symbol);
            },
            "symbol"_a, byrefint)
        .def_prop_ro("options", [](const PyAnalysisManager& self) -> const AnalysisOptions& {
            return self.manager.getOptions();
        });

    nb::class_<ReadRange>(m, "ReadRange")
        .def_ro("symbol", &ReadRange::symbol)
        .def_ro("bitRange", &ReadRange::bitRange);

    nb::enum_<SensitivityList::Kind>(m, "SensitivityListKind")
        .value("None_", SensitivityList::Kind::None)
        .value("Explicit", SensitivityList::Kind::Explicit)
        .value("Implicit", SensitivityList::Kind::Implicit)
        .value("Dynamic", SensitivityList::Kind::Dynamic);

    nb::class_<SensitivityList>(m, "SensitivityList")
        .def_ro("kind", &SensitivityList::kind)
        .def_ro("timingControl", &SensitivityList::timingControl)
        .def_prop_ro("reads", [](const SensitivityList& s) -> std::span<const ReadRange> {
            return s.reads;
        });

    nb::class_<AnalyzedProcedure::ImplicitEventReadSet>(m, "ImplicitEventReadSet")
        .def_ro("statement", &AnalyzedProcedure::ImplicitEventReadSet::statement)
        .def_prop_ro("reads",
                     [](const AnalyzedProcedure::ImplicitEventReadSet& s)
                         -> std::span<const ReadRange> { return s.reads; });

    nb::class_<AnalyzedProcedure>(m, "AnalyzedProcedure")
        .def_ro("analyzedSymbol", &AnalyzedProcedure::analyzedSymbol)
        .def_ro("parentProcedure", &AnalyzedProcedure::parentProcedure)
        .def_prop_ro("inferredClock", &AnalyzedProcedure::getInferredClock)
        .def_prop_ro("drivers", &AnalyzedProcedure::getDrivers)
        .def_prop_ro("callExpressions", &AnalyzedProcedure::getCallExpressions)
        .def_prop_ro("timingControls", &AnalyzedProcedure::getTimingControls)
        .def_prop_ro("readSet", &AnalyzedProcedure::getReadSet)
        .def_prop_ro("implicitEventReadSets", &AnalyzedProcedure::getImplicitEventReadSets)
        .def_prop_ro("sensitivityList", &AnalyzedProcedure::getSensitivityList);

    nb::class_<AnalyzedAssertion>(m, "AnalyzedAssertion")
        .def_ro("containingSymbol", &AnalyzedAssertion::containingSymbol)
        .def_ro("procedure", &AnalyzedAssertion::procedure)
        .def_ro("astNode", &AnalyzedAssertion::astNode)
        .def_prop_ro("semanticLeadingClock", &AnalyzedAssertion::getSemanticLeadingClock)
        .def_prop_ro("root", &AnalyzedAssertion::getRoot)
        .def("getClock", &AnalyzedAssertion::getClock, "expr"_a, byrefint);

    nb::class_<PyFlowAnalysis>(
        m, "FlowAnalysis",
        "A flow analysis visitor that walks statements with proper control flow "
        "handling.\n\n"
        "Set callback attributes before calling run():\n"
        "- onAssignment: called for each assignment expression\n"
        "- onVariableRef: called for each variable reference "
        "(NamedValueExpression)\n"
        "- onCallExpression: called for each function/task call\n"
        "- onConditionalBegin: called when entering an if/else\n"
        "- onCaseBegin: called when entering a case statement\n"
        "- onLoopBegin: called when entering any loop statement\n"
        "- onBranchMerge: called when control flow paths merge (state1, state2) "
        "-> merged_state\n"
        "- onStateCopy: called to copy state when forking (state) -> "
        "copied_state\n"
        "- createTopState: called to create initial state () -> state")
        .def(nb::init<const Symbol&, AnalysisOptions>(), "symbol"_a,
             "options"_a = AnalysisOptions(),
             "Create a flow analysis for the given symbol (procedural block, "
             "subroutine, etc.)")
        .def(
            "run", [](PyFlowAnalysis& self, const Statement& stmt) { self.run(stmt); }, "stmt"_a,
            "Run the analysis on a statement")
        .def(
            "run", [](PyFlowAnalysis& self, const Expression& expr) { self.run(expr); }, "expr"_a,
            "Run the analysis on an expression")
        .def_prop_rw("currentState", &PyFlowAnalysis::getCurrentState,
                     &PyFlowAnalysis::setCurrentState, "The current flow state's user data")
        .def_prop_ro("bad", &PyFlowAnalysis::isBad, "True if the analysis detected an error")
        .def_prop_ro("evalContext", &PyFlowAnalysis::getEvalCtx, byrefint,
                     "The evaluation context for use during analysis")
        .def_rw("onAssignment", &PyFlowAnalysis::onAssignment,
                "Callback for assignment expressions: (AssignmentExpression) -> None")
        .def_rw("onVariableRef", &PyFlowAnalysis::onVariableRef,
                "Callback for variable references: (NamedValueExpression) -> None")
        .def_rw("onCallExpression", &PyFlowAnalysis::onCallExpression,
                "Callback for function/task calls: (CallExpression) -> None")
        .def_rw("onConditionalBegin", &PyFlowAnalysis::onConditionalBegin,
                "Callback when entering conditional: (ConditionalStatement) -> None")
        .def_rw("onCaseBegin", &PyFlowAnalysis::onCaseBegin,
                "Callback when entering case: (CaseStatement) -> None")
        .def_rw("onLoopBegin", &PyFlowAnalysis::onLoopBegin,
                "Callback when entering any loop: (Statement) -> None")
        .def_rw("onBranchMerge", &PyFlowAnalysis::onBranchMerge,
                "Callback when branches merge: (state1, state2) -> merged_state")
        .def_rw("onStateCopy", &PyFlowAnalysis::onStateCopy,
                "Callback to copy state: (state) -> copied_state")
        .def_rw("createTopState", &PyFlowAnalysis::createTopState,
                "Callback to create initial state: () -> state");
}
