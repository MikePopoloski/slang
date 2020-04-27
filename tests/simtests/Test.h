#pragma once

#include <catch2/catch.hpp>

#include "slang/codegen/CodeGenerator.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/mir/MIRBuilder.h"
#include "slang/mir/Procedure.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/syntax/SyntaxTree.h"

using namespace slang;
using namespace slang::mir;

inline Compilation compile(const std::string& text) {
    Compilation compilation;
    compilation.addSyntaxTree(SyntaxTree::fromText(text));

    auto& diags = compilation.getAllDiagnostics();
    if (!diags.empty()) {
        std::string report =
            DiagnosticEngine::reportAll(SyntaxTree::getDefaultSourceManager(), diags);
        FAIL_CHECK(report);
    }

    return compilation;
}