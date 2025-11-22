//------------------------------------------------------------------------------
// AnalysisBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/AnalysisOptions.h"
#include "slang/text/SourceManager.h"

using namespace slang::analysis;

void registerAnalysis(py::module_& m) {
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
}
