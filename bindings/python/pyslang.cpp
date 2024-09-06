//------------------------------------------------------------------------------
// pyslang.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

void registerAST(py::module_& m);
void registerCompilation(py::module_& m);
void registerExpressions(py::module_& m);
void registerNumeric(py::module_& m);
void registerUtil(py::module_& m);
void registerStatements(py::module_& m);
void registerSymbols(py::module_& m);
void registerSyntax(py::module_& m);
void registerSyntaxNodes0(py::module_& m);
void registerSyntaxNodes1(py::module_& m);
void registerSyntaxNodes2(py::module_& m);
void registerSyntaxNodes3(py::module_& m);
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
    registerExpressions(m);
    registerNumeric(m);
    registerUtil(m);
    registerStatements(m);
    registerSymbols(m);
    registerSyntax(m);
    registerSyntaxNodes0(m);
    registerSyntaxNodes1(m);
    registerSyntaxNodes2(m);
    registerSyntaxNodes3(m);
    registerTypes(m);

    py::register_exception_translator([](std::exception_ptr p) {
        try {
            if (p)
                std::rethrow_exception(p);
        }
        catch (const std::filesystem::filesystem_error& e) {
            const auto code = e.code();
            const auto p1 = e.path1().string();
            const auto p2 = e.path2().string();
            PyErr_SetObject(PyExc_IOError,
                            py::make_tuple(code.value(), code.message(),
                                           p1.empty() ? py::none() : py::cast(p1), code.value(),
                                           p2.empty() ? py::none() : py::cast(p2))
                                .ptr());
        }
    });
}
