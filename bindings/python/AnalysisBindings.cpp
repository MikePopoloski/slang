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
        .def_readonly("childScopes", &AnalyzedScope::childScopes)
        .def_readonly("procedures", &AnalyzedScope::procedures);

    py::classh<PendingAnalysis>(m, "PendingAnalysis")
        .def_readonly("symbol", &PendingAnalysis::symbol)
        .def("tryGet", &PendingAnalysis::tryGet, byrefint);

    py::classh<AnalyzedDesign>(m, "AnalyzedDesign")
        .def_readonly("compilation", &AnalyzedDesign::compilation)
        .def_readonly("compilationUnits", &AnalyzedDesign::compilationUnits)
        .def_readonly("packages", &AnalyzedDesign::packages)
        .def_readonly("topInstances", &AnalyzedDesign::topInstances);

    py::classh<ValueDriver>(m, "ValueDriver")
        .def_readonly("prefixExpression", &ValueDriver::prefixExpression)
        .def_readonly("containingSymbol", &ValueDriver::containingSymbol)
        .def_readonly("procCallExpression", &ValueDriver::procCallExpression)
        .def_readonly("flags", &ValueDriver::flags)
        .def_readonly("kind", &ValueDriver::kind)
        .def_readonly("source", &ValueDriver::source)
        .def_readonly("isFromSideEffect", &ValueDriver::isFromSideEffect)
        .def_property_readonly("sourceRange", &ValueDriver::getSourceRange)
        .def_property_readonly("isInputPort", &ValueDriver::isInputPort)
        .def_property_readonly("isUnidirectionalPort", &ValueDriver::isUnidirectionalPort)
        .def_property_readonly("isClockVar", &ValueDriver::isClockVar)
        .def_property_readonly("isInSingleDriverProcedure",
                               &ValueDriver::isInSingleDriverProcedure);

    py::classh<AnalysisManager>(m, "AnalysisManager")
        .def(py::init<AnalysisOptions>(), "options"_a = AnalysisOptions())
        .def("analyze", &AnalysisManager::analyze, "compilation"_a)
        .def("getDrivers", &AnalysisManager::getDrivers, "symbol"_a, byrefint)
        .def("getDiagnostics", &AnalysisManager::getDiagnostics, "sourceManager"_a)
        .def("analyzeScopeBlocking", &AnalysisManager::analyzeScopeBlocking, "scope"_a,
             "parentProcedure"_a = nullptr, byrefint)
        .def("getAnalyzedScope", &AnalysisManager::getAnalyzedScope, "scope"_a, byrefint)
        .def("getAnalyzedSubroutine", &AnalysisManager::getAnalyzedSubroutine, "symbol"_a, byrefint)
        .def_property_readonly("options", &AnalysisManager::getOptions);

    py::classh<AnalyzedProcedure>(m, "AnalyzedProcedure")
        .def_readonly("analyzedSymbol", &AnalyzedProcedure::analyzedSymbol)
        .def_readonly("parentProcedure", &AnalyzedProcedure::parentProcedure)
        .def_property_readonly("inferredClock", &AnalyzedProcedure::getInferredClock)
        .def_property_readonly("assertions", &AnalyzedProcedure::getAssertions)
        .def_property_readonly("drivers", &AnalyzedProcedure::getDrivers)
        .def_property_readonly("callExpressions", &AnalyzedProcedure::getCallExpressions);
}
