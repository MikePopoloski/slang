//------------------------------------------------------------------------------
// Lazy.h
// Helper types for lazy elaboration.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "util/PointerUnion.h"

namespace slang {

class Expression;
class Scope;
class Symbol;
class Type;
struct DataTypeSyntax;
struct ExpressionSyntax;

template<typename TDerived, typename TResult, typename TSource>
struct Lazy {
    using ScopeOrSymbol = PointerUnion<const Scope*, const Symbol*>;

    Lazy(ScopeOrSymbol parent, const TResult* init) : parent(parent), cache(init) {}
    Lazy(ScopeOrSymbol parent, const TSource& init) : parent(parent), cache(&init) {}

    Lazy& operator=(const TResult* result) { cache = result; return *this; }
    Lazy& operator=(const TResult& result) { cache = &result; return *this; }
    Lazy& operator=(const TSource& source) { cache = &source; return *this; }

    const TResult& operator*() const { return *get(); }

    const TResult* operator->() const { return get(); }

    explicit operator bool() const { return get(); }

    const TResult* get() const {
        if (cache.index() == 0)
            return std::get<0>(cache);

        auto derived = static_cast<const TDerived*>(this);
        const TResult& result = derived->evaluate(getScope(), *std::get<1>(cache));
        cache = &result;
        return &result;
    }

    const TSource* getSourceOrNull() const {
        if (cache.index() == 0)
            return nullptr;
        return std::get<1>(cache);
    }

    bool hasResult() const { return cache.index() == 0 && std::get<0>(cache); }

protected:
    const Scope& getScope() const {
        if (parent.is<const Symbol*>())
            return *parent.get<const Symbol*>()->getScope();
        else
            return *parent.get<const Scope*>();
    }

private:
    ScopeOrSymbol parent;
    mutable std::variant<const TResult*, const TSource*> cache;
};

#define LAZY(name, TResult, TSource)                            \
    struct name : public Lazy<name, TResult, TSource> {         \
        explicit name(ScopeOrSymbol parent);                    \
        name(ScopeOrSymbol parent, const TResult* init) :       \
            Lazy<name, TResult, TSource>(parent, init) {}       \
        name(ScopeOrSymbol parent, const TSource& init) :       \
            Lazy<name, TResult, TSource>(parent, init) {}       \
        using Lazy<name, TResult, TSource>::operator=;          \
    private:                                                    \
        friend struct Lazy<name, TResult, TSource>;             \
        const TResult& evaluate(const Scope& scope, const TSource& source) const; \
    }

LAZY(LazyInitializer, Expression, ExpressionSyntax);
LAZY(LazyType, Type, DataTypeSyntax);

#undef LAZY

}