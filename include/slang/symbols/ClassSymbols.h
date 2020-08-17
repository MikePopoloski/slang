//------------------------------------------------------------------------------
//! @file ClassSymbols.h
//! @brief Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/symbols/Type.h"

namespace slang {

struct ClassDeclarationSyntax;

/// Represents a class definition type.
class ClassType : public Type, public Scope {
public:
    ClassType(Compilation& compilation, string_view name, SourceLocation loc);

    static const Type& fromSyntax(const Scope& scope, const ClassDeclarationSyntax& syntax);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassType; }
};

} // namespace slang
