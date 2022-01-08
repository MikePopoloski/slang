//------------------------------------------------------------------------------
//! @file CoverSymbols.h
//! @brief Contains coverage-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/types/DeclaredType.h"
#include "slang/types/Type.h"

namespace slang {

class FormalArgumentSymbol;
struct CovergroupDeclarationSyntax;

/// Represents the body of a covergroup type, separated out because the
/// arguments of a covergroup need to live in their own scope so that
/// they can be shadowed by body members.
class CovergroupBodySymbol : public Symbol, public Scope {
public:
    CovergroupBodySymbol(Compilation& compilation, SourceLocation loc) :
        Symbol(SymbolKind::CovergroupBody, ""sv, loc), Scope(compilation, this) {}

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CovergroupBody; }
};

/// Represents a covergroup definition type.
class CovergroupType : public Type, public Scope {
public:
    span<const FormalArgumentSymbol* const> arguments;
    const CovergroupBodySymbol& body;

    CovergroupType(Compilation& compilation, string_view name, SourceLocation loc,
                   const CovergroupBodySymbol& body);

    static const Symbol& fromSyntax(const Scope& scope, const CovergroupDeclarationSyntax& syntax);

    const TimingControl* getCoverageEvent() const;
    ConstantValue getDefaultValueImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CovergroupType; }

private:
    mutable optional<const TimingControl*> event;
};

struct CoverpointSyntax;

class CoverpointSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredType;

    CoverpointSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    static CoverpointSymbol& fromSyntax(const Scope& scope, const CoverpointSyntax& syntax);

    const Type& getType() const { return declaredType.getType(); }

    const Expression& getCoverageExpr() const {
        auto init = declaredType.getInitializer();
        ASSERT(init);
        return *init;
    }

    const Expression* getIffExpr() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Coverpoint; }

private:
    mutable optional<const Expression*> iffExpr;
};

struct CoverCrossSyntax;

class CoverCrossSymbol : public Symbol, public Scope {
public:
    CoverCrossSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::CoverCross, name, loc), Scope(compilation, this) {}

    static CoverCrossSymbol& fromSyntax(const Scope& scope, const CoverCrossSyntax& syntax);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CoverCross; }
};

} // namespace slang
