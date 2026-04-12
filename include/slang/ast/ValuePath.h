//------------------------------------------------------------------------------
//! @file ValuePath.h
//! @brief A path to some subset of a value symbol
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Function.h"
#include "slang/util/Iterator.h"
#include "slang/util/Util.h"

namespace slang {
class BumpAllocator;
}

namespace slang::ast {

class EvalContext;
class Expression;
class Type;
class ValueSymbol;

/// Represents a path to some subset of a value symbol, such as via field
/// accesses or array element selects.
///
/// Some portions of the path may be statically known, if they have constant
/// select value or are for known struct fields. Others are only dynamically
/// known, such as non-constant selects, dynamic array accesses, class handle
/// member access, virtual interface access, etc.
///
/// Leading elements of the path that are statically known form a "static prefix".
/// The longest such prefix is the "longest static prefix" which the LRM uses
/// as a way to specify legal and illegal conditions for assignments.
class SLANG_EXPORT ValuePath {
public:
    /// The root of the path.
    ///
    /// Note that it is possible for @a rootSymbol to be nullptr but @a fullExpr to be
    /// non-null, in cases like selects of a concat: `{a, b}[0]` and selects of a function
    /// call result: `foo().bar`. Note that such a path is not considered a static prefix.
    const ValueSymbol* rootSymbol = nullptr;

    /// The type of the root of the path.
    ///
    /// This will be non-null if @a fullExpr is non-null, even if @a rootSymbol is
    /// otherwise null due to a path selecting from a concat.
    const Type* rootType = nullptr;

    /// The full expression representing the path.
    ///
    /// This can be nullptr if, for example, shrinkToLSP() is called
    /// on a path that does not have a static prefix.
    const Expression* fullExpr = nullptr;

    /// The portion of the path that is the longest static prefix, if any.
    ///
    /// This can be nullptr if there are no static prefixes of the path.
    const Expression* lsp = nullptr;

    /// If the path has a longest static prefix, the bit range selected by that prefix.
    std::pair<uint64_t, uint64_t> lspBounds;

    /// Constructs an empty path.
    ValuePath() {}

    /// Constructs a new value path from a path expression.
    ValuePath(const Expression& expr, EvalContext& evalContext);

    /// Visits all value paths in the provided arbitrary expression,
    /// invoking the callback for each one.
    ///
    /// If @a skipSelectors is true this function won't visit expressions inside
    /// selectors, such as `a` and `b` in `foo[a:b]`. It also won't visit the
    /// lhs of class and virtual interface handle accesses.
    static void visitPaths(const Expression& expr, EvalContext& evalContext,
                           function_ref<void(const ValuePath&)> callback,
                           bool skipSelectors = false);

    /// Returns a new path that represents the current path with all dynamic components
    /// removed, such that the resulting path is just the longest static prefix.
    [[nodiscard]] ValuePath shrinkToLSP() const;

    /// Clones the path into a new one that represents the same path but with all constant
    /// select expressions baked into constants in the expression tree.
    [[nodiscard]] ValuePath clone(BumpAllocator& alloc, EvalContext& evalContext) const;

    /// Retargets the value path to a new root. The new target must have the same type
    /// as the existing root type. The path cannot be empty.
    [[nodiscard]] ValuePath retarget(BumpAllocator& alloc, EvalContext& evalContext,
                                     const ValueSymbol& target) const;

    /// Returns true if the path is empty, meaning it has no root or path components.
    [[nodiscard]] bool empty() const { return !rootType || !fullExpr; }

    /// Returns true if the path is fully static (i.e. has no dynamic components).
    [[nodiscard]] bool isFullyStatic() const { return fullExpr == lsp; }

    /// Returns true if this path overlaps @a other.
    [[nodiscard]] bool overlaps(const ValuePath& other) const;

    /// Returns a humany-friendly string representation of the path.
    [[nodiscard]] std::string toString(EvalContext& evalContext) const;

    /// An iterator for components of the path.
    class iterator : public iterator_facade<iterator> {
    public:
        /// Constructs a default iterator that points nowhere.
        iterator() : expr(nullptr) {}

        /// Constructs an iterator pointing at the given path component.
        iterator(const Expression* expr) : expr(expr) {}

        /// Dereferences the iterator, resolving it to an expression.
        const Expression& dereference() const { return *expr; }

        /// Advances the iterator to the next component in the path.
        void increment();

        /// @returns true if the given iterator is equal to this one.
        bool equals(const iterator& other) const { return expr == other.expr; }

    private:
        const Expression* expr;
    };

    /// Gets an iterator to the "start" of the path, which is the *outermost* expression.
    iterator begin() const { return iterator(fullExpr); }

    /// Gets an iterator to the end of the path, which is one past the root of the path.
    iterator end() const { return iterator(); }
};

} // namespace slang::ast
