//------------------------------------------------------------------------------
//! @file AssertionExpr.h
//! @brief Assertion expression creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/ASTSerializer.h"
#include "slang/util/Util.h"

namespace slang {

// clang-format off
#define EXPR(x) \
    x(Invalid)
ENUM(AssertionExprKind, EXPR);
#undef EXPR
// clang-format on

class BindContext;
class Compilation;
class SyntaxNode;
struct PropertyExprSyntax;
struct SequenceExprSyntax;

class AssertionExpr {
public:
    AssertionExprKind kind;

    const SyntaxNode* syntax = nullptr;

    bool bad() const { return kind == AssertionExprKind::Invalid; }

    static const AssertionExpr& bind(const SequenceExprSyntax& syntax, const BindContext& context);
    static const AssertionExpr& bind(const PropertyExprSyntax& syntax, const BindContext& context);

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
    explicit AssertionExpr(AssertionExprKind kind) : kind(kind) {}

    static AssertionExpr& badExpr(Compilation& compilation, const AssertionExpr* expr);
};

class InvalidAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr* child;

    explicit InvalidAssertionExpr(const AssertionExpr* child) :
        AssertionExpr(AssertionExprKind::Invalid), child(child) {}

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

} // namespace slang
