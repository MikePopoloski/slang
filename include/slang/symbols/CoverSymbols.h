//------------------------------------------------------------------------------
//! @file CoverSymbols.h
//! @brief Contains coverage-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/types/Type.h"

namespace slang {

class FormalArgumentSymbol;
struct CovergroupDeclarationSyntax;

/// Represents a covergroup definition type.
class CovergroupType : public Type, public Scope {
public:
    span<const FormalArgumentSymbol* const> arguments;

    CovergroupType(Compilation& compilation, string_view name, SourceLocation loc);

    static const Symbol& fromSyntax(const Scope& scope, const CovergroupDeclarationSyntax& syntax);

    ConstantValue getDefaultValueImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CovergroupType; }
};

} // namespace slang
