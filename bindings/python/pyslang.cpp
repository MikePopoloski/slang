//------------------------------------------------------------------------------
// pyslang.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

void registerAnalysis(nb::module_& m, nb::module_& ast);
void registerAST(nb::module_& m);
void registerCompilation(nb::module_& m, nb::module_& ast, nb::module_& driver);
void registerExpressions(nb::module_& m);
void registerNumeric(nb::module_& m);
void registerDiagnostics(nb::module_& m);
void registerText(nb::module_& m);
void registerUtil(nb::module_& m);
void registerStatements(nb::module_& m);
void registerSymbols(nb::module_& m);
void registerSyntax(nb::module_& syntax, nb::module_& parsing);
void registerSyntaxNodes0(nb::module_& m);
void registerSyntaxNodes1(nb::module_& m);
void registerSyntaxNodes2(nb::module_& m);
void registerSyntaxNodes3(nb::module_& m);
void registerSyntaxFactory(nb::module_& m);
void registerTypes(nb::module_& m);

NB_MODULE(pyslang, m) {
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

    registerAnalysis(analysis, ast);
    registerAST(ast);
    registerCompilation(m, ast, driver);
    registerExpressions(ast);
    registerNumeric(m);
    registerDiagnostics(m);
    registerText(m);
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

    // nanobind exception translators take a `(const std::exception_ptr&,
    // void*)` callback (a non-capturing lambda convertible to a function
    // pointer). If this translator does not handle the exception it simply lets
    // it propagate, and nanobind falls back to the next (default) translator.
    nb::register_exception_translator([](const std::exception_ptr& p, void* /*payload*/) {
        try {
            if (p)
                std::rethrow_exception(p);
        }
        catch (const std::filesystem::filesystem_error& e) {
            const auto code = e.code();
            const auto p1 = e.path1().string();
            const auto p2 = e.path2().string();
            PyErr_SetObject(PyExc_IOError,
                            nb::make_tuple(code.value(), code.message(),
                                           p1.empty() ? nb::none() : nb::cast(p1), code.value(),
                                           p2.empty() ? nb::none() : nb::cast(p2))
                                .ptr());
        }
    });
}
