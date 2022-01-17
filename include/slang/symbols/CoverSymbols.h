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

    bool isTypeOption() const;
    string_view getName() const;
    const Expression& getExpression() const;

private:
    not_null<const Scope*> scope;
    not_null<const CoverageOptionSyntax*> syntax;
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
    span<const FormalArgumentSymbol* const> sampleArguments;
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

class BinsSelectExpr;
struct BinsSelectionSyntax;
struct CoverageBinsSyntax;
struct TransRangeSyntax;

class CoverageBinSymbol : public Symbol {
public:
    struct TransRangeList {
        span<const Expression* const> items;
        const Expression* repeatFrom = nullptr;
        const Expression* repeatTo = nullptr;
        enum RepeatKind { None, Consecutive, Nonconsecutive, GoTo } repeatKind = None;

        TransRangeList(const TransRangeSyntax& syntax, const Type& type,
                       const BindContext& context);
    };

    using TransSet = span<const TransRangeList>;

    enum BinKind { Bins, IllegalBins, IgnoreBins } binsKind = Bins;
    bool isArray = false;
    bool isWildcard = false;
    bool isDefault = false;
    bool isDefaultSequence = false;

    CoverageBinSymbol(string_view name, SourceLocation loc) :
        Symbol(SymbolKind::CoverageBin, name, loc) {}

    const Expression* getIffExpr() const;
    const Expression* getNumberOfBinsExpr() const;
    const Expression* getSetCoverageExpr() const;
    const Expression* getWithExpr() const;
    const BinsSelectExpr* getCrossSelectExpr() const;
    span<const Expression* const> getValues() const;
    span<const TransSet> getTransList() const;

    void serializeTo(ASTSerializer& serializer) const;

    static CoverageBinSymbol& fromSyntax(const Scope& scope, const CoverageBinsSyntax& syntax);
    static CoverageBinSymbol& fromSyntax(const Scope& scope, const BinsSelectionSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CoverageBin; }

private:
    void resolve() const;

    mutable const Expression* numberOfBinsExpr = nullptr;
    mutable const Expression* iffExpr = nullptr;
    mutable const Expression* setCoverageExpr = nullptr;
    mutable const Expression* withExpr = nullptr;
    mutable const BinsSelectExpr* selectExpr = nullptr;
    mutable span<const Expression* const> values;
    mutable span<const TransSet> transList;
    mutable bool isResolved = false;
};

struct CoverpointSyntax;
struct IdentifierNameSyntax;

class CoverpointSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredType;
    span<const CoverageOptionSetter> options;

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

/// Represents the body of a cover cross type, separated out because the
/// members of the cross body can't be accessed outside of the cross itself.
class CoverCrossBodySymbol : public Symbol, public Scope {
public:
    CoverCrossBodySymbol(Compilation& compilation, SourceLocation loc) :
        Symbol(SymbolKind::CoverCrossBody, ""sv, loc), Scope(compilation, this) {}

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CoverCrossBody; }
};

struct CoverCrossSyntax;

class CoverCrossSymbol : public Symbol, public Scope {
public:
    span<const CoverpointSymbol* const> targets;
    span<const CoverageOptionSetter> options;

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

// clang-format off
#define EXPR(x) \
    x(Invalid) \
    x(Condition) \
    x(Binary) \
    x(CrossSet)
ENUM(BinsSelectExprKind, EXPR)
#undef EXPR
// clang-format on

struct BinsSelectExpressionSyntax;

class BinsSelectExpr {
public:
    BinsSelectExprKind kind;

    const SyntaxNode* syntax = nullptr;

    bool bad() const { return kind == BinsSelectExprKind::Invalid; }

    static const BinsSelectExpr& bind(const BinsSelectExpressionSyntax& syntax,
                                      const BindContext& context);

    template<typename T>
    T& as() {
        ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    explicit BinsSelectExpr(BinsSelectExprKind kind) : kind(kind) {}

    static BinsSelectExpr& badExpr(Compilation& compilation, const BinsSelectExpr* expr);
};

class InvalidBinsSelectExpr : public BinsSelectExpr {
public:
    const BinsSelectExpr* child;

    explicit InvalidBinsSelectExpr(const BinsSelectExpr* child) :
        BinsSelectExpr(BinsSelectExprKind::Invalid), child(child) {}

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct BinsSelectConditionExprSyntax;

class ConditionBinsSelectExpr : public BinsSelectExpr {
public:
    ConditionBinsSelectExpr() : BinsSelectExpr(BinsSelectExprKind::Condition) {}

    static BinsSelectExpr& fromSyntax(const BinsSelectConditionExprSyntax& syntax,
                                      const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::Condition; }
};

} // namespace slang
