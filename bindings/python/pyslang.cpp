//------------------------------------------------------------------------------
// pyslang.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

void registerAST(py::module_& m);
void registerCompilation(py::module_& m);
void registerNumeric(py::module_& m);
void registerUtil(py::module_& m);
void registerSymbols(py::module_& m);
void registerSyntax(py::module_& m);
void registerSyntaxNodes(py::module_& m);
void registerTypes(py::module_& m);

PYBIND11_MODULE(pyslang, m) {
    m.doc() = "Python bindings for slang, the SystemVerilog compiler library";

#ifdef VERSION_INFO
    m.attr("__version__") = MACRO_STRINGIFY(VERSION_INFO);
#else
    m.attr("__version__") = "dev";
#endif

    registerAST(m);
    registerCompilation(m);
    registerNumeric(m);
    registerUtil(m);
    registerSymbols(m);
    registerSyntax(m);
    registerSyntaxNodes(m);
    registerTypes(m);
}
