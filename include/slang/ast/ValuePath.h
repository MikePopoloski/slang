//------------------------------------------------------------------------------
//! @file ValuePath.h
//! @brief A path to some subset of a value symbol
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>
#include <vector>

#include "slang/numeric/ConstantValue.h"
#include "slang/util/Function.h"
#include "slang/util/Hash.h"
#include "slang/util/Iterator.h"
#include "slang/util/PointerIntPair.h"
#include "slang/util/Util.h"

namespace slang {
class BumpAllocator;
}

namespace slang::ast {

class EvalContext;
class Expression;
class Type;
class ValueSymbol;

/// The elements of a dynamically sized array that a longest static prefix selects
/// into with a constant index or key, reached from a variable. Bits within one unit
/// of storage are addressed by offset; the elements of a dynamically sized array
/// have no offset in the storage that holds the array, so they are a unit of their own.
struct SLANG_EXPORT ElementStorage {
    /// A select into the elements of a dynamically sized array.
    struct Step {
        /// The bit offset of the array within the storage that holds it.
        uint64_t arrayOffset;

        /// The key selected, for an associative array, whose element at each
        /// key is storage of its own. Empty for a dynamic array or a queue,
        /// whose elements together are one unit of storage laid out by index.
        ConstantValue key;

        bool operator==(const Step&) const = default;

        /// Computes a hash of the array offset and the key.
        size_t hash() const;
    };

    /// The variable that holds the storage.
    not_null<const ValueSymbol*> symbol;

    /// The selects that lead from the variable to the storage, nearest the variable first.
    std::vector<Step> steps;

    bool operator==(const ElementStorage&) const = default;

    /// Computes a hash of the variable and the selects.
    size_t hash() const;
};

/// Names a unit of storage that a longest static prefix can lie in: a variable,
/// or the elements of a dynamically sized array held in one. It is the size of
/// a pointer, so naming a variable costs no more than its symbol does.
class SLANG_EXPORT StorageLocation {
public:
    /// Names the storage of a variable.
    explicit StorageLocation(const ValueSymbol& symbol) : pip(&symbol, false) {}

    /// Names the elements described by @a elements, which must outlive this name.
    explicit StorageLocation(const ElementStorage& elements) : pip(&elements, true) {}

    /// Gets the variable that holds the storage.
    [[nodiscard]] const ValueSymbol& getSymbol() const {
        if (auto elements = getElements())
            return *elements->symbol;
        return *static_cast<const ValueSymbol*>(pip.getPointer());
    }

    /// Gets the elements named, or nullptr if the storage is the variable itself.
    [[nodiscard]] const ElementStorage* getElements() const {
        return pip.getInt() ? static_cast<const ElementStorage*>(pip.getPointer()) : nullptr;
    }

    /// Gets the selects that lead from the variable to the storage, nearest the
    /// variable first; there are none if the storage is the variable itself.
    [[nodiscard]] std::span<const ElementStorage::Step> getSteps() const {
        if (auto elements = getElements())
            return elements->steps;
        return {};
    }

    bool operator==(const StorageLocation& rhs) const {
        if (pip == rhs.pip)
            return true;

        auto elements = getElements();
        auto rhsElements = rhs.getElements();
        return elements && rhsElements && *elements == *rhsElements;
    }

private:
    PointerIntPair<const void*, 1, 1, bool> pip;
};

/// The bits that a longest static prefix covers in the storage it lies in.
struct SLANG_EXPORT StoragePlace {
    /// The storage the bits are in.
    StorageLocation location;

    /// The range of bits covered within that storage.
    std::pair<uint64_t, uint64_t> bitRange;
};

/// Represents a path to some subset of a value symbol, such as via field
/// accesses or array element selects.
///
/// Some portions of the path may be statically known, if they have constant
/// select value or are for known struct fields. Others are only dynamically
/// known, such as non-constant selects, class handle member access, virtual
/// interface access, etc.
///
/// Leading elements of the path that are statically known form a "static prefix".
/// The longest such prefix is the "longest static prefix" which the LRM uses
/// as a way to specify legal and illegal conditions for assignments.
class SLANG_EXPORT ValuePath {
public:
    /// The root of the path.
    const Expression* rootExpr = nullptr;

    /// The full expression representing the path.
    const Expression* fullExpr = nullptr;

    /// The portion of the path that is the longest static prefix, if any.
    ///
    /// This can be nullptr if there is no static prefix of the path.
    const Expression* lsp = nullptr;

    /// If the path has a longest static prefix, the bit range selected by that prefix.
    /// Where the prefix goes on into the elements of a dynamically sized array, which
    /// have no bits in the root, this is the bit range of the first such array.
    std::pair<uint64_t, uint64_t> lspBounds;

    /// Constructs an empty path.
    ValuePath() = default;

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

    /// Gets the value symbol at the root of the path, if there is one.
    [[nodiscard]] const ValueSymbol* rootSymbol() const;

    /// Returns true if the path is empty, meaning it has no root or path components.
    [[nodiscard]] bool empty() const { return fullExpr == nullptr; }

    /// Returns true if the path is fully static (i.e. has no dynamic components).
    [[nodiscard]] bool isFullyStatic() const { return fullExpr == lsp; }

    /// Returns true if the longest static prefix selects into the elements of a
    /// dynamically sized array; lspBounds is then the one bit of the first such array.
    [[nodiscard]] bool isLSPInElements() const {
        return lsp && lsp != rootExpr && lspBounds.first == lspBounds.second &&
               selectsIntoElements();
    }

    /// Gets the part of the longest static prefix @a lsp that lies in the fixed
    /// layout of its root: @a lsp itself, or, where it selects into the elements
    /// of a dynamically sized array, the expression that names the first such array.
    [[nodiscard]] static const Expression& getFixedLayoutPrefix(const Expression& lsp);

    /// Returns true if this path overlaps @a other.
    [[nodiscard]] bool overlaps(const ValuePath& other) const;

    /// Gets the storage that the longest static prefix lies in and the bits it
    /// covers there, for a prefix that selects into the elements of a dynamically
    /// sized array. @a keepElements is handed those elements and returns the copy
    /// that the place is to name.
    [[nodiscard]] StoragePlace getLSPPlace(
        EvalContext& evalContext,
        function_ref<const ElementStorage&(ElementStorage&&)> keepElements) const;

    /// Returns a humany-friendly string representation of the path.
    [[nodiscard]] std::string toString(EvalContext& evalContext) const;

    /// Clones the path into a new one that represents the same path but with all constant
    /// select expressions baked into constants in the expression tree.
    [[nodiscard]] ValuePath clone(BumpAllocator& alloc, EvalContext& evalContext) const;

    /// Retargets the value path to a new root. The new target must have the same type
    /// as the existing root type. The path cannot be empty.
    [[nodiscard]] ValuePath retarget(BumpAllocator& alloc, EvalContext& evalContext,
                                     const ValueSymbol& target) const;

    /// Expands indirect references (via explicit modport port and ref port connections)
    /// and visits the resulting paths with the provided callback. If this path does not
    /// contain such references, the callback will be invoked once with *this.
    void expandIndirectRefs(BumpAllocator& alloc, EvalContext& evalContext,
                            function_ref<void(const ValuePath&)> callback) const;

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

private:
    bool selectsIntoElements() const;
};

} // namespace slang::ast

namespace slang {

template<>
struct hash<ast::ElementStorage::Step> {
    size_t operator()(const ast::ElementStorage::Step& step) const { return step.hash(); }
};

template<>
struct hash<ast::StorageLocation> {
    size_t operator()(const ast::StorageLocation& location) const {
        if (auto elements = location.getElements())
            return elements->hash();
        return hash<const ast::ValueSymbol*>()(&location.getSymbol());
    }
};

} // namespace slang
