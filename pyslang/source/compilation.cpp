//------------------------------------------------------------------------------
// compilation.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Compilation.h"

#include "pyslang.h"

void registerCompilation(py::module_& m) {
    py::enum_<MinTypMax>(m, "MinTypMax")
        .value("Min", MinTypMax::Min)
        .value("Typ", MinTypMax::Typ)
        .value("Max", MinTypMax::Max);

    py::class_<CompilationOptions>(m, "CompilationOptions")
        .def(py::init<>())
        .def_readwrite("maxInstanceDepth", &CompilationOptions::maxInstanceDepth)
        .def_readwrite("maxGenerateSteps", &CompilationOptions::maxGenerateSteps)
        .def_readwrite("maxConstexprDepth", &CompilationOptions::maxConstexprDepth)
        .def_readwrite("maxConstexprSteps", &CompilationOptions::maxConstexprSteps)
        .def_readwrite("maxConstexprBacktrace", &CompilationOptions::maxConstexprBacktrace)
        .def_readwrite("maxDefParamSteps", &CompilationOptions::maxDefParamSteps)
        .def_readwrite("errorLimit", &CompilationOptions::errorLimit)
        .def_readwrite("typoCorrectionLimit", &CompilationOptions::typoCorrectionLimit)
        .def_readwrite("minTypMax", &CompilationOptions::minTypMax)
        .def_readwrite("allowHierarchicalConst", &CompilationOptions::allowHierarchicalConst)
        .def_readwrite("relaxEnumConversions", &CompilationOptions::relaxEnumConversions)
        .def_readwrite("allowDupInitialDrivers", &CompilationOptions::allowDupInitialDrivers)
        .def_readwrite("strictDriverChecking", &CompilationOptions::strictDriverChecking)
        .def_readwrite("lintMode", &CompilationOptions::lintMode)
        .def_readwrite("suppressUnused", &CompilationOptions::suppressUnused)
        .def_readwrite("topModules", &CompilationOptions::topModules)
        .def_readwrite("paramOverrides", &CompilationOptions::paramOverrides);
}
