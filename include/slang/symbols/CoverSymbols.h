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
struct CoverageOptionSyntax;
struct CovergroupDeclarationSyntax;

class CoverageOptionSetter {
public:
    CoverageOptionSetter(const Scope& scope, const CoverageOptionSyntax& syntax);

    string_view getName() const;
    const Expression& getExpression() const;

private:
    const Scope& scope;
    const CoverageOptionSyntax& syntax;
    mutable const Expression* expr = nullptr;
};

/// Represents the body of a covergroup type, separated out because the
/// arguments of a covergroup need to live in their own scope so that
/// they can be shadowed by body members.
class CovergroupBodySymbol : public Symbol, public Scope {
public:
    span<const CoverageOptionSetter> options;

    CovergroupBodySymbol(Compilation& compilation, SourceLocation loc);

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
struct IdentifierNameSyntax;

class CoverpointSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredType;

    CoverpointSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    static CoverpointSymbol& fromSyntax(const Scope& scope, const CoverpointSyntax& syntax);
    static CoverpointSymbol& fromImplicit(const Scope& scope, const IdentifierNameSyntax& syntax);

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
    span<const CoverpointSymbol* const> targets;

    CoverCrossSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     span<const CoverpointSymbol* const> targets);

    static void fromSyntax(const Scope& scope, const CoverCrossSyntax& syntax,
                           SmallVector<const Symbol*>& results);

    const Expression* getIffExpr() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CoverCross; }

private:
    mutable optional<const Expression*> iffExpr;
};

} // namespace slang
