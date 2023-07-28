//------------------------------------------------------------------------------
//! @file SvTypeReflector.h
//! @brief Top level of the type reflector library
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include "CppEmitter.h"

#include "slang/ast/Compilation.h"

class SvTypeReflector {
public:
    explicit SvTypeReflector(std::unique_ptr<slang::ast::Compilation> compilation, bool verbose,
                             bool noSystemC) :
        compilation(std::move(compilation)),
        verbose(verbose), noSystemC(noSystemC), cppEmitter(noSystemC) {}

    void reflect();

    std::string emit() { return cppEmitter.emit(); }
    void emitToFile(const fs::path& path) { cppEmitter.emitToFile(path); }

private:
    bool verbose;
    bool noSystemC;
    CppEmitter cppEmitter;
    std::unique_ptr<slang::ast::Compilation> compilation;
};
