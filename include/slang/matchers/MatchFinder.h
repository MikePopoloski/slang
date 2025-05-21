//------------------------------------------------------------------------------
//! @file MatchFinder.h
//! @brief Class that tries to find the nodes that matches the rules provided
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "MatchersInternal.h"

namespace slang::ast::matchers {

class MatchResult {
public:
    explicit MatchResult(const BoundNodesMap& boundNodes, ASTContext& context) :
        boundNodes(boundNodes), context(context) {}

    template<typename T>
    std::optional<const T*> getNodeAs(const std::string& id) const {
        if (const auto it = boundNodes.find(id); it != boundNodes.end()) {
            return it->second->as<const T>();
        }
        return {};
    }

private:
    const BoundNodesMap& boundNodes;
    ASTContext& context;
};

class MatcherCallback {
public:
    virtual ~MatcherCallback() = default;
    virtual void run(const MatchResult& result) = 0;
};

class MatchFinder : public ASTVisitor<MatchFinder, true, true> {
    struct MatcherEntry {
        internal::BindableMatcher matcher;
        MatcherCallback* callback;
    };
    std::vector<MatcherEntry> matchers;
    ASTContext context; // Our simple context

    void innerMatch(const Symbol& symbol, const Symbol* parent = nullptr) {
        for (const auto& [matcher, callback] : matchers) {
            BoundNodesMap boundNodes;

            if (matcher.matches(symbol, context, boundNodes)) {
                MatchResult result(boundNodes, context);
                callback->run(result);
            }
        }
    }

public:
    explicit MatchFinder(const ASTContext& context) : context(context) {}

    void addMatcher(const internal::BindableMatcher& matcher, MatcherCallback* callback) {
        matchers.push_back({matcher, callback});
    }

    template<typename T>
    void match(const T& rootNode, const Symbol* parent = nullptr) {
        visit(rootNode);
    }

    template<typename T>
    void visit(const T& t) {
        if constexpr (std::is_base_of_v<Symbol, T>)
            innerMatch(t, nullptr);
        visitDefault(t);
    }
};
} // namespace slang::ast::matchers
