//------------------------------------------------------------------------------
// pyslang.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

void registerAnalysis(py::module_& m, py::module_& ast);
void registerAST(py::module_& m);
void registerCompilation(py::module_& m, py::module_& ast, py::module_& driver);
void registerExpressions(py::module_& m);
void registerNumeric(py::module_& m);
void registerDiagnostics(py::module_& m);
void registerText(py::module_& m);
void registerUtil(py::module_& m);
void registerStatements(py::module_& m);
void registerSymbols(py::module_& m);
void registerSyntax(py::module_& syntax, py::module_& parsing);
void registerSyntaxNodes0(py::module_& m);
void registerSyntaxNodes1(py::module_& m);
void registerSyntaxNodes2(py::module_& m);
void registerSyntaxNodes3(py::module_& m);
void registerSyntaxFactory(py::module_& m);
void registerTypes(py::module_& m);

PYBIND11_MODULE(pyslang, m) {
    m.doc() = "Python bindings for slang, the SystemVerilog compiler library";

#ifdef VERSION_INFO
    m.attr("__version__") = MACRO_STRINGIFY(VERSION_INFO);
#else
    m.attr("__version__") = "dev";
#endif

    auto ast = m.def_submodule("ast", "AST types: symbols, expressions, statements, types");
    auto syntax = m.def_submodule("syntax", "Syntax tree nodes and utilities");
    auto parsing = m.def_submodule("parsing", "Lexer, parser, preprocessor types");
    auto analysis = m.def_submodule("analysis", "Code analysis utilities");
    auto driver = m.def_submodule("driver", "Compilation driver");
    auto numeric = m.def_submodule("numeric", "Numeric types: SVInt, ConstantValue");
    auto diagnostics = m.def_submodule("diagnostics", "Diagnostic engine and types");
    auto text = m.def_submodule("text", "Source management utilities");

    registerAnalysis(analysis, ast);
    registerAST(ast);
    registerCompilation(m, ast, driver);
    registerExpressions(ast);
    registerNumeric(numeric);
    registerDiagnostics(diagnostics);
    registerText(text);
    registerUtil(m);
    registerStatements(ast);
    registerSymbols(ast);
    registerSyntax(syntax, parsing);
    registerSyntaxNodes0(syntax);
    registerSyntaxNodes1(syntax);
    registerSyntaxNodes2(syntax);
    registerSyntaxNodes3(syntax);
    registerSyntaxFactory(syntax);
    registerTypes(ast);

    for (auto& submod : {ast, syntax, parsing, numeric, diagnostics, text, driver, analysis}) {
        for (auto item : submod.attr("__dict__").cast<py::dict>()) {
            auto name = item.first.cast<std::string>();
            if (name[0] != '_' && !py::hasattr(m, name.c_str())) {
                m.attr(name.c_str()) = item.second;
            }
        }
    }

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
