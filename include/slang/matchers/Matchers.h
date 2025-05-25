//------------------------------------------------------------------------------
//! @file Matchers.h
//! @brief AST Matchers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include "MatchersInternal.h"

#include "slang/ast/Symbol.h"
#include "slang/ast/symbols/VariableSymbols.h"

namespace slang::ast::matchers {

template<typename NodeType>
class GenericMatcher final : public internal::Matcher<NodeType> {
public:
    bool matches(const Symbol& node, ASTContext&, BoundNodesMap&) const override {
        return node.as_if<NodeType>() != nullptr;
    }
};

class VarDeclMatcher final : public internal::ComposableMatcher<VariableSymbol> {
public:
    VarDeclMatcher() = default;

    template<typename... MatcherArgs>
    explicit VarDeclMatcher(MatcherArgs... matchers) : ComposableMatcher(matchers...) {}

    bool matches(const VariableSymbol& varDecl, ASTContext& context,
                 BoundNodesMap& boundNodes) const override {
        for (const auto& matcher : matchers) {
            if (!matcher.matches(varDecl, context, boundNodes)) {
                return false;
            }
        }
        return true;
    }
};

inline internal::BindableMatcher varDecl() {
    return internal::BindableMatcher(VarDeclMatcher());
}

template<typename... MatcherArgs>
internal::BindableMatcher varDecl(MatcherArgs... innerMatchers) {
    return internal::BindableMatcher(VarDeclMatcher(innerMatchers...));
}

} // namespace slang::ast::matchers
