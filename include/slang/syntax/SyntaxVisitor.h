//------------------------------------------------------------------------------
//! @file SyntaxVisitor.h
//! @brief Syntax tree visitor support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <functional>
#include <utility>

#include "slang/parsing/Token.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxNode.h"

namespace slang::syntax {

#define DERIVED *static_cast<TDerived*>(this)

/// Use this type as a base class for syntax tree visitors. It will default to
/// traversing all children of each node. Add implementations for any specific
/// node types you want to handle.
template<typename TDerived>
struct SyntaxVisitor {
public:
    /// Visit the provided node, of static type T.
    template<typename T>
    void visit(const T& t) {
        if constexpr (requires { (DERIVED).handle(t); })
            (DERIVED).handle(t);
        else if constexpr (requires { (DERIVED)(DERIVED, t); })
            (DERIVED)(DERIVED, t);
        else
            visitDefault(t);
    }

    /// The default handler invoked when no visit() method is overridden for a particular type.
    /// Will visit all child nodes by default.
    void visitDefault(const SyntaxNode& node) {
        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (child)
                child->visit(DERIVED);
            else {
                auto token = node.childToken(i);
                if (token)
                    (DERIVED).visitToken(token);
            }
        }
    }

private:
    // This is to make things compile if the derived class doesn't provide an implementation.
    void visitToken(parsing::Token) {}
};

/// @brief Creates a SyntaxVisitor out of the provided handler functions.
///
/// The provided callable arguments must take two parameters, the first of which
/// is the visitor object itself (so that you can call visitDefault on it if
/// desired) and the second is the Syntax type to match against.
///
/// For example, to create a visitor that will count all of the HierarchicalInstance nodes
/// in a Syntax Tree:
///
/// @code
/// int count = 0;
/// makeSyntaxVisitor([&](auto& visitor, const HierarchicalInstanceSyntax& node) {
///     count++;
///     visitor.visitDefault(node);
/// })
/// @endcode
///
template<typename... Functions>
auto makeSyntaxVisitor(Functions... funcs) {
    struct Result : public Functions..., public SyntaxVisitor<Result> {
        Result(Functions... funcs) : Functions(std::move(funcs))... {}
        using Functions::operator()...;
    };
    return Result(std::move(funcs)...);
}

/// @brief Simple visitors with kinds that are left to the user to evaluate.
/// This is preferable over makeSyntaxVisitor([](auto, auto){...}), as the compile time cost is
/// lower, and the compiler errors are better.
struct AllSyntaxVisitor {
    AllSyntaxVisitor(std::function<void(const SyntaxNode&)> func) : handler(std::move(func)) {}

    void visit(const SyntaxNode& node) {
        handler(node);
        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (child)
                visit(*child);
        }
    }

private:
    std::function<void(const SyntaxNode&)> handler;
};

#undef DERIVED

} // namespace slang::syntax
