//------------------------------------------------------------------------------
//! @file CoverSymbols.h
//! @brief Contains coverage-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/ast/Scope.h"
#include "slang/ast/types/DeclaredType.h"
#include "slang/ast/types/Type.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Function.h"

namespace slang::ast {

class FormalArgumentSymbol;

class SLANG_EXPORT CoverageOptionSetter {
public:
    CoverageOptionSetter(const Scope& scope, const syntax::CoverageOptionSyntax& syntax);

    bool isTypeOption() const;
    std::string_view getName() const;
    const Expression& getExpression() const;

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return getExpression().visit(visitor);
    }

private:
    not_null<const Scope*> scope;
    not_null<const syntax::CoverageOptionSyntax*> syntax;
    mutable const Expression* expr = nullptr;
};

/// Represents the body of a covergroup type, separated out because the
/// arguments of a covergroup need to live in their own scope so that
/// they can be shadowed by body members.
class SLANG_EXPORT CovergroupBodySymbol : public Symbol, public Scope {
public:
    std::span<const CoverageOptionSetter> options;

    CovergroupBodySymbol(Compilation& compilation, SourceLocation loc);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CovergroupBody; }

private:
    friend class CovergroupType;

    const Symbol* lastBuiltinMember = nullptr;
};

/// Represents a covergroup definition type.
class SLANG_EXPORT CovergroupType : public Type, public Scope {
public:
    using ArgList = std::span<const FormalArgumentSymbol* const>;

    CovergroupType(Compilation& compilation, std::string_view name, SourceLocation loc,
                   const CovergroupBodySymbol& body);

    ArgList getArguments() const {
        ensureElaborated();
        return arguments;
    }

    const CovergroupBodySymbol& getBody() const {
        ensureElaborated();
        return body;
    }

    const Type* getBaseGroup() const {
        ensureElaborated();
        return baseGroup;
    }

    const TimingControl* getCoverageEvent() const;
    ConstantValue getDefaultValueImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static const CovergroupType& fromSyntax(const Scope& scope,
                                            const syntax::CovergroupDeclarationSyntax& syntax,
                                            const Symbol*& classProperty);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CovergroupType; }

private:
    friend class Scope;

    void inheritMembers(function_ref<void(const Symbol&)> insertCB) const;

    const CovergroupBodySymbol& body;
    mutable ArgList arguments;
    mutable std::optional<const TimingControl*> event;
    mutable const Type* baseGroup = nullptr;
};

class BinsSelectExpr;

class SLANG_EXPORT CoverageBinSymbol : public Symbol {
public:
    struct TransRangeList {
        std::span<const Expression* const> items;
        const Expression* repeatFrom = nullptr;
        const Expression* repeatTo = nullptr;
        enum RepeatKind { None, Consecutive, Nonconsecutive, GoTo } repeatKind = None;

        TransRangeList(const syntax::TransRangeSyntax& syntax, const Type& type,
                       const ASTContext& context);

        void serializeTo(ASTSerializer& serializer) const;

        template<typename TVisitor>
        void visitExprs(TVisitor&& visitor) const {
            for (auto item : items)
                item->visit(visitor);

            if (repeatFrom)
                repeatFrom->visit(visitor);

            if (repeatTo)
                repeatTo->visit(visitor);
        }
    };

    using TransSet = std::span<const TransRangeList>;

    enum BinKind { Bins, IllegalBins, IgnoreBins } binsKind = Bins;
    bool isArray = false;
    bool isWildcard = false;
    bool isDefault = false;
    bool isDefaultSequence = false;

    CoverageBinSymbol(std::string_view name, SourceLocation loc) :
        Symbol(SymbolKind::CoverageBin, name, loc) {}

    const Expression* getIffExpr() const;
    const Expression* getNumberOfBinsExpr() const;
    const Expression* getSetCoverageExpr() const;
    const Expression* getWithExpr() const;
    const BinsSelectExpr* getCrossSelectExpr() const;
    std::span<const Expression* const> getValues() const;
    std::span<const TransSet> getTransList() const;

    void serializeTo(ASTSerializer& serializer) const;

    static CoverageBinSymbol& fromSyntax(const Scope& scope,
                                         const syntax::CoverageBinsSyntax& syntax);
    static CoverageBinSymbol& fromSyntax(const Scope& scope,
                                         const syntax::BinsSelectionSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CoverageBin; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const;

private:
    void resolve() const;

    mutable const Expression* numberOfBinsExpr = nullptr;
    mutable const Expression* iffExpr = nullptr;
    mutable const Expression* setCoverageExpr = nullptr;
    mutable const Expression* withExpr = nullptr;
    mutable const BinsSelectExpr* selectExpr = nullptr;
    mutable std::span<const Expression* const> values;
    mutable std::span<const TransSet> transList;
    mutable bool isResolved = false;
};

class SLANG_EXPORT CoverpointSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredType;
    std::span<const CoverageOptionSetter> options;

    CoverpointSymbol(Compilation& compilation, std::string_view name, SourceLocation loc);

    static CoverpointSymbol& fromSyntax(const Scope& scope, const syntax::CoverpointSyntax& syntax);
    static CoverpointSymbol& fromImplicit(const Scope& scope,
                                          const syntax::IdentifierNameSyntax& syntax);

    const Type& getType() const { return declaredType.getType(); }

    const Expression& getCoverageExpr() const {
        auto init = declaredType.getInitializer();
        SLANG_ASSERT(init);
        return *init;
    }

    const Expression* getIffExpr() const;

    void checkBins() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Coverpoint; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (auto expr = getIffExpr())
            expr->visit(visitor);

        for (auto& opt : options)
            opt.visitExprs(visitor);
    }

private:
    mutable std::optional<const Expression*> iffExpr;
    bool isImplicit = false;
};

/// Represents the body of a cover cross type, separated out because the
/// members of the cross body can't be accessed outside of the cross itself.
class SLANG_EXPORT CoverCrossBodySymbol : public Symbol, public Scope {
public:
    const Type* crossQueueType = nullptr;

    CoverCrossBodySymbol(Compilation& compilation, SourceLocation loc) :
        Symbol(SymbolKind::CoverCrossBody, ""sv, loc), Scope(compilation, this) {}

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CoverCrossBody; }
};

class SLANG_EXPORT CoverCrossSymbol : public Symbol, public Scope {
public:
    std::span<const CoverpointSymbol* const> targets;
    std::span<const CoverageOptionSetter> options;

    CoverCrossSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                     std::span<const CoverpointSymbol* const> targets);

    static CoverCrossSymbol& fromSyntax(const Scope& scope, const syntax::CoverCrossSyntax& syntax,
                                        SmallVectorBase<const Symbol*>& implicitMembers);

    const Expression* getIffExpr() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CoverCross; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (auto expr = getIffExpr())
            expr->visit(visitor);

        for (auto& opt : options)
            opt.visitExprs(visitor);
    }

private:
    friend class Scope;

    void addBody(const syntax::CoverCrossSyntax& syntax, const Scope& scope);

    mutable std::optional<const Expression*> iffExpr;
};

// clang-format off
#define EXPR(x) \
    x(Invalid) \
    x(Condition) \
    x(Unary) \
    x(Binary) \
    x(SetExpr) \
    x(WithFilter) \
    x(CrossId)
SLANG_ENUM(BinsSelectExprKind, EXPR)
#undef EXPR
// clang-format on

class SLANG_EXPORT BinsSelectExpr {
public:
    BinsSelectExprKind kind;

    const syntax::SyntaxNode* syntax = nullptr;

    BinsSelectExpr(const BinsSelectExpr&) = delete;
    BinsSelectExpr& operator=(const BinsSelectExpr&) = delete;

    bool bad() const { return kind == BinsSelectExprKind::Invalid; }

    static const BinsSelectExpr& bind(const syntax::BinsSelectExpressionSyntax& syntax,
                                      const ASTContext& context);

    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    explicit BinsSelectExpr(BinsSelectExprKind kind) : kind(kind) {}

    static BinsSelectExpr& badExpr(Compilation& compilation, const BinsSelectExpr* expr);
};

class SLANG_EXPORT InvalidBinsSelectExpr : public BinsSelectExpr {
public:
    const BinsSelectExpr* child;

    explicit InvalidBinsSelectExpr(const BinsSelectExpr* child) :
        BinsSelectExpr(BinsSelectExprKind::Invalid), child(child) {}

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

class SLANG_EXPORT ConditionBinsSelectExpr : public BinsSelectExpr {
public:
    const Symbol& target;
    std::span<const Expression* const> intersects;

    explicit ConditionBinsSelectExpr(const Symbol& target) :
        BinsSelectExpr(BinsSelectExprKind::Condition), target(target) {}

    static BinsSelectExpr& fromSyntax(const syntax::BinsSelectConditionExprSyntax& syntax,
                                      const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::Condition; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto expr : intersects)
            expr->visit(visitor);
    }
};

class SLANG_EXPORT UnaryBinsSelectExpr : public BinsSelectExpr {
public:
    const BinsSelectExpr& expr;

    /// The kind of unary operator. Currently there's only one such kind of
    /// operator supported in SystemVerilog.
    enum Op { Negation } op = Negation;

    explicit UnaryBinsSelectExpr(const BinsSelectExpr& expr) :
        BinsSelectExpr(BinsSelectExprKind::Unary), expr(expr) {}

    static BinsSelectExpr& fromSyntax(const syntax::UnaryBinsSelectExprSyntax& syntax,
                                      const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::Unary; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

class SLANG_EXPORT BinaryBinsSelectExpr : public BinsSelectExpr {
public:
    const BinsSelectExpr& left;
    const BinsSelectExpr& right;
    enum Op { And, Or } op;

    BinaryBinsSelectExpr(const BinsSelectExpr& left, const BinsSelectExpr& right, Op op) :
        BinsSelectExpr(BinsSelectExprKind::Binary), left(left), right(right), op(op) {}

    static BinsSelectExpr& fromSyntax(const syntax::BinaryBinsSelectExprSyntax& syntax,
                                      const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::Binary; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left.visit(visitor);
        right.visit(visitor);
    }
};

class SLANG_EXPORT SetExprBinsSelectExpr : public BinsSelectExpr {
public:
    const Expression& expr;
    const Expression* matchesExpr;

    SetExprBinsSelectExpr(const Expression& expr, const Expression* matchesExpr) :
        BinsSelectExpr(BinsSelectExprKind::SetExpr), expr(expr), matchesExpr(matchesExpr) {}

    static BinsSelectExpr& fromSyntax(const syntax::SimpleBinsSelectExprSyntax& syntax,
                                      const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::SetExpr; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        if (matchesExpr)
            matchesExpr->visit(visitor);
    }
};

class SLANG_EXPORT BinSelectWithFilterExpr : public BinsSelectExpr {
public:
    const BinsSelectExpr& expr;
    const Expression& filter;
    const Expression* matchesExpr;

    BinSelectWithFilterExpr(const BinsSelectExpr& expr, const Expression& filter,
                            const Expression* matchesExpr) :
        BinsSelectExpr(BinsSelectExprKind::WithFilter), expr(expr), filter(filter),
        matchesExpr(matchesExpr) {}

    static BinsSelectExpr& fromSyntax(const syntax::BinSelectWithFilterExprSyntax& syntax,
                                      const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::WithFilter; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        filter.visit(visitor);
        if (matchesExpr)
            matchesExpr->visit(visitor);
    }
};

class SLANG_EXPORT CrossIdBinsSelectExpr : public BinsSelectExpr {
public:
    CrossIdBinsSelectExpr() : BinsSelectExpr(BinsSelectExprKind::CrossId) {}

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(BinsSelectExprKind kind) { return kind == BinsSelectExprKind::CrossId; }
};

template<typename TVisitor>
void CoverageBinSymbol::visitExprs(TVisitor&& visitor) const {
    if (auto expr = getIffExpr())
        expr->visit(visitor);
    if (auto expr = getNumberOfBinsExpr())
        expr->visit(visitor);
    if (auto expr = getSetCoverageExpr())
        expr->visit(visitor);
    if (auto expr = getWithExpr())
        expr->visit(visitor);
    if (auto expr = getCrossSelectExpr())
        expr->visit(visitor);

    for (auto val : getValues())
        val->visit(visitor);

    for (auto& set : getTransList()) {
        for (auto& rangeList : set)
            rangeList.visitExprs(visitor);
    }
}

} // namespace slang::ast
