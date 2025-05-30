//------------------------------------------------------------------------------
//! @file Matchers.h
//! @brief AST Matchers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "MatchersUtils.h"
#include <map>
#include <string>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Symbol.h"

namespace slang::ast::matchers {

using BoundNodesMap = std::map<std::string, const Symbol*>;

namespace internal {

/**
 * Base matcher class, all matcher shall derive from it
 * @tparam NodeType AST Node the matcher is matching against
 */
template<typename NodeType>
class Matcher {
public:
    virtual ~Matcher() = default;

    virtual bool matches(const NodeType& node, ASTContext& context,
                         BoundNodesMap& boundNodes) const = 0;
};

/**
 * Base matcher class, that allows to `bind()` the result of the match to an ID
 */
class BindableMatcher {
public:
    template<typename MatcherImp>
    explicit BindableMatcher(const MatcherImp& matcher) {
        using NodeType = typename ExtractNodeType<MatcherImp>::type;

        static_assert(std::is_base_of_v<Matcher<NodeType>, MatcherImp>,
                      "MatherImp must be derived from Matcher");

        auto matcherCopy = std::make_shared<MatcherImp>(matcher);
        matcherFunc = [matcherCopy](const Symbol& node, ASTContext& context,
                                    BoundNodesMap& boundNodes) {
            if (const NodeType* specificNode = node.as_if<NodeType>()) {
                return matcherCopy->matches(*specificNode, context, boundNodes);
            }
            return false;
        };
    }

    BindableMatcher(std::function<bool(const Symbol&, ASTContext&, BoundNodesMap&)>&& func,
                    const std::string&& id) : matcherFunc(func), boundId(id) {}

    bool matches(const Symbol& symbol, ASTContext& context, BoundNodesMap& boundNodes) const {
        const bool match = matcherFunc(symbol, context, boundNodes);
        if (match && !boundId.empty()) {
            boundNodes[boundId] = &symbol;
        }
        return match;
    }

    BindableMatcher bind(const std::string&& id) {
        return BindableMatcher(std::move(matcherFunc), std::forward<const std::string>(id));
    }

private:
    std::function<bool(const Symbol&, ASTContext&, BoundNodesMap&)> matcherFunc;
    const std::string boundId;
};

template<typename NodeType>
class ComposableMatcher : public Matcher<NodeType> {
public:
    template<typename... Matchers>
    explicit ComposableMatcher(Matchers... matchers) : matchers({BindableMatcher(matchers)...}) {}

protected:
    std::vector<BindableMatcher> matchers;
};

} // namespace internal

} // namespace slang::ast::matchers
