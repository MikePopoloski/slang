//------------------------------------------------------------------------------
//! @file SyntaxNode.h
//! @brief Base class and utilities for syntax nodes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cstring>
#include <ranges>
#include <span>
#include <string>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxKind.h"
#include "slang/util/Iterator.h"
#include "slang/util/PointerIntPair.h"
#include "slang/util/SmallVector.h"

namespace slang::syntax {

class SyntaxNode;

namespace detail {

struct SyntaxParentInfo {
    SyntaxNode* parent = nullptr;
    const SyntaxNode* previewNode = nullptr;
};

} // namespace detail

/// A token pointer or a syntax node pointer.
struct SLANG_EXPORT PtrTokenOrSyntax {
    PtrTokenOrSyntax(parsing::Token* token) :
        value(reinterpret_cast<uintptr_t>(token) | TokenTag) {}
    PtrTokenOrSyntax(SyntaxNode* node) : value(reinterpret_cast<uintptr_t>(node)) {}
    PtrTokenOrSyntax(nullptr_t) : value(TokenTag) {}

    /// @return true if the object is a token.
    bool isToken() const { return (value & TokenTag) != 0; }

    /// @return true if the object is a syntax node.
    bool isNode() const { return !isToken(); }

    /// Gets access to the object as a token (asserting if it's not actually a token).
    parsing::Token* token() const {
        SLANG_ASSERT(isToken());
        return reinterpret_cast<parsing::Token*>(value & ~TokenTag);
    }

    /// Gets access to the object as a syntax node (asserting if it's not actually a node).
    SyntaxNode* node() const {
        SLANG_ASSERT(isNode());
        return reinterpret_cast<SyntaxNode*>(value);
    }

    /// Gets the source range for the token or syntax node or NoLocation if it
    /// points to nullptr.
    SourceRange range() const;

private:
    static constexpr uintptr_t TokenTag = 0x1u;
    uintptr_t value;
};

/// A token or a constant syntax node.
struct SLANG_EXPORT ConstTokenOrSyntax {
    ConstTokenOrSyntax(parsing::Token token) : storage(token) {}
    ConstTokenOrSyntax(const SyntaxNode* node) {
        // The pointer is shifted down by 1 to guarantee that the
        // top bit is clear, which is where the token tag bit is set.
        storage.nodePtr = reinterpret_cast<uintptr_t>(node) >> 1;
    }
    ConstTokenOrSyntax(nullptr_t) : storage(parsing::Token()) {}

    /// @return true if the object is a token.
    bool isToken() const { return parsing::Token::storageHasTokenTag(&storage); }

    /// @return true if the object is a syntax node.
    bool isNode() const { return !isToken(); }

    /// Gets access to the object as a token (asserting if it's not actually a token).
    parsing::Token token() const {
        SLANG_ASSERT(isToken());
        return storage.tok;
    }

    /// Gets access to the object as a syntax node (asserting if it's not actually a node).
    const SyntaxNode* node() const {
        SLANG_ASSERT(isNode());
        return reinterpret_cast<const SyntaxNode*>(storage.nodePtr << 1);
    }

    /// Gets the source range for the token or syntax node.
    SourceRange range() const;

protected:
    union Storage {
        byte empty[sizeof(parsing::Token)] = {};
        parsing::Token tok;
        uintptr_t nodePtr;

        Storage(parsing::Token t) : tok(t) {}
        Storage() {}
    } storage;
};

/// A token or a syntax node.
struct SLANG_EXPORT TokenOrSyntax : public ConstTokenOrSyntax {
    TokenOrSyntax(parsing::Token token) : ConstTokenOrSyntax(token) {}
    TokenOrSyntax(SyntaxNode* node) : ConstTokenOrSyntax(node) {}
    TokenOrSyntax(nullptr_t) : ConstTokenOrSyntax(parsing::Token()) {}

    /// Gets access to the object as a syntax node (asserting if it's not actually a node).
    SyntaxNode* node() const {
        // const_cast is safe because we only could have constructed this
        // object with a non-const pointer.
        return const_cast<SyntaxNode*>(ConstTokenOrSyntax::node());
    }

    /// Gets a mutable pointer to the stored token (asserting if it's not actually a token).
    parsing::Token* tokenPtr() {
        SLANG_ASSERT(isToken());
        return &storage.tok;
    }
};

/// Base class for all syntax nodes.
class SLANG_EXPORT SyntaxNode {
public:
    using Token = parsing::Token;

    /// @brief A small proxy that behaves like a `SyntaxNode*` but stores
    /// its pointer in a tagged form so that the low bit can be used to
    /// indicate the rare presence of a "preview node" attached to this
    /// node (see `previewNode()` below).
    ///
    /// When the low bit is clear, the stored value is a plain pointer
    /// to the parent SyntaxNode. When set, the value points instead at
    /// a `detail::SyntaxParentInfo` struct (allocated from the same
    /// BumpAllocator that owns the syntax tree) which holds both the
    /// real parent pointer and the preview node pointer.
    class ParentRef {
    public:
        ParentRef() = default;
        ParentRef(SyntaxNode* p) : raw(reinterpret_cast<uintptr_t>(p)) {}

        ParentRef& operator=(SyntaxNode* p) {
            if (raw & TagBit)
                reinterpret_cast<detail::SyntaxParentInfo*>(raw & ~TagBit)->parent = p;
            else
                raw = reinterpret_cast<uintptr_t>(p);
            return *this;
        }

        operator SyntaxNode*() const { return get(); }
        SyntaxNode* operator->() const { return get(); }
        SyntaxNode& operator*() const { return *get(); }

        SyntaxNode* get() const {
            if (raw & TagBit)
                return reinterpret_cast<detail::SyntaxParentInfo*>(raw & ~TagBit)->parent;
            return reinterpret_cast<SyntaxNode*>(raw);
        }

    private:
        friend class SyntaxNode;

        static constexpr uintptr_t TagBit = 0x1u;

        bool isTagged() const { return (raw & TagBit) != 0; }

        SyntaxNode* getRaw() const { return reinterpret_cast<SyntaxNode*>(raw); }

        detail::SyntaxParentInfo* getInfo() const {
            SLANG_ASSERT(isTagged());
            return reinterpret_cast<detail::SyntaxParentInfo*>(raw & ~TagBit);
        }

        void setInfo(detail::SyntaxParentInfo* info) {
            raw = reinterpret_cast<uintptr_t>(info) | TagBit;
        }

        uintptr_t raw = 0;
    };

    /// The kind of syntax node.
    SyntaxKind kind;

    /// The parent node of this syntax node. The root of the syntax
    /// tree does not have a parent (will be nullptr).
    ///
    /// This behaves like a `SyntaxNode*`, but internally tags its low
    /// bit to record the (rare) presence of an attached preview node.
    /// See `ParentRef` above for details.
    ParentRef parent;

    /// @brief Returns the optional "preview" syntax node associated
    /// with this node, or nullptr if none.
    ///
    /// Preview nodes can be useful to know ahead of time when visiting
    /// this node. The node, if set, is underneath this node in the
    /// syntax tree.
    ///
    /// For example, an enum declaration deep inside an expression tree
    /// needs to be known up front to add its members to its parent scope.
    ///
    /// Preview nodes are very rare in practice, so we avoid storing a
    /// dedicated pointer in every `SyntaxNode`. Instead, when one is
    /// attached we allocate a small `detail::SyntaxParentInfo` struct
    /// from the syntax tree's BumpAllocator and tag the parent pointer to
    /// reach it.
    const SyntaxNode* previewNode() const {
        return parent.isTagged() ? parent.getInfo()->previewNode : nullptr;
    }

    /// Sets the preview node associated with this node. Passing
    /// nullptr removes any existing preview node entry.
    ///
    /// The first time a preview node is attached to a particular
    /// SyntaxNode, a small indirection struct is allocated from the
    /// provided BumpAllocator. The allocator must be the same one
    /// that owns the memory for this syntax tree, since the
    /// indirection struct's lifetime is tied to it.
    void setPreviewNode(BumpAllocator& alloc, const SyntaxNode* node) {
        if (!node && !parent.isTagged())
            return;
        setPreviewNodeImpl(alloc, node);
    }

    /// Print the node and all of its children to a string.
    std::string toString() const;

    /// Get the first leaf token in this subtree.
    Token getFirstToken() const;

    /// Get the last leaf token in this subtree.
    Token getLastToken() const;

    /// Get the first leaf token as a mutable pointer in this subtree.
    Token* getFirstTokenPtr();

    /// Get the last leaf token a mutable pointer in this subtree.
    Token* getLastTokenPtr();

    /// Get the source range of the node.
    SourceRange sourceRange() const;

    /// Gets the child syntax node at the specified index. If the child at
    /// the given index is not a node (probably a token) then this returns null.
    const SyntaxNode* childNode(size_t index) const;

    /// Gets the child syntax node at the specified index. If the child at
    /// the given index is not a node (probably a token) then this returns null.
    SyntaxNode* childNode(size_t index);

    /// Gets the child token at the specified index. If the child at
    /// the given index is not a token (probably a node) then this returns
    /// an empty Token.
    Token childToken(size_t index) const;

    /// Gets a pointer to the child token at the specified index. If the
    /// child at the given index is not a token (probably a node) then
    /// this returns null.
    Token* childTokenPtr(size_t index);

    /// Gets the number of (direct) children underneath this node in the tree.
    size_t getChildCount() const; // Note: implemented in AllSyntax.cpp

    /// An iterator that walks through all tokens in a syntax node in order.
    class SLANG_EXPORT token_iterator : public iterator_facade<token_iterator> {
    public:
        token_iterator() : node(nullptr), childIndex(0), currentToken() {}

        parsing::Token dereference() const { return currentToken; }

        void increment();

        bool equals(const token_iterator& other) const;

    private:
        friend class SyntaxNode;

        explicit token_iterator(const SyntaxNode* node);

        void findNextToken();

        const SyntaxNode* node;
        size_t childIndex;
        parsing::Token currentToken;
        SmallVector<std::pair<const SyntaxNode*, size_t>, 4> stack;
    };

    /// Gets an iterator to the first token in this subtree.
    token_iterator tokens_begin() const { return token_iterator(this); }

    /// Gets an iterator representing the end of tokens in this subtree.
    token_iterator tokens_end() const { return token_iterator(); }

    /// Returns true if this syntax node is "equivalent" to the other provided
    /// syntax node. Equivalence here is determined by the entire subtrees having
    /// the same kinds of syntax nodes in the same order and all leaf tokens
    /// having the same kinds and value text.
    bool isEquivalentTo(const SyntaxNode& other) const;

    /// Reinterprets this node as being of type T. In debug this will assert
    /// that the dynamic kind is appropriate for the specified static type.
    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    /// Reinterprets this node as being of type T. In debug this will assert
    /// that the dynamic kind is appropriate for the specified static type.
    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    // Reinterprets this node as being of type T, if it is not belong type T, return nullptr
    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    // Reinterprets this node as being of type T, if it is not belong type T, return nullptr
    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    /// Applies a visitor object to this node by dispatching based on the
    /// dynamic kind. The given @a args are forwarded to the visitor.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor&& visitor, Args&&... args);

    /// Applies a visitor object to this node by dispatching based on the
    /// dynamic kind. The given @a args are forwarded to the visitor.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor&& visitor, Args&&... args) const;

    /// A base implemention of the method that checks correctness of dynamic casting.
    /// Derived nodes should reimplement this and return true if the provided syntax kind
    /// is compatible with the static type of the object.
    static bool isKind(SyntaxKind) { return true; }

    /// Derived nodes should implement this and return true if child at provided
    /// index is pointer not wrapped in not_null.
    static bool isChildOptional(size_t) { return true; }

protected:
    explicit SyntaxNode(SyntaxKind kind) : kind(kind) {}

private:
    void setPreviewNodeImpl(BumpAllocator& alloc, const SyntaxNode* node);

    ConstTokenOrSyntax getChild(size_t index) const;
    TokenOrSyntax getChild(size_t index);
    PtrTokenOrSyntax getChildPtr(size_t index);
};

/// @brief Performs a shallow clone of the given syntax node.
///
/// All members will be simply copied to the new instance.
/// The instance will be allocated with the provided allocator.
SLANG_EXPORT SyntaxNode* clone(const SyntaxNode& node, BumpAllocator& alloc);

/// @brief Performs a deep clone of the given syntax node.
///
/// All members will be cloned recursively to create a complete new
/// copy of the syntax tree. All cloned instances will be allocated
/// with the provided allocator.
SLANG_EXPORT SyntaxNode* deepClone(const SyntaxNode& node, BumpAllocator& alloc);

/// @brief Performs a shallow clone of the given syntax node.
///
/// All members will be simply copied to the new instance.
/// The instance will be allocated with the provided allocator.
template<std::derived_from<SyntaxNode> T>
T* clone(const T& node, BumpAllocator& alloc) {
    return static_cast<T*>(clone(static_cast<const SyntaxNode&>(node), alloc));
}

/// @brief Performs a deep clone of the given syntax node.
///
/// All members will be cloned recursively to create a complete new
/// copy of the syntax tree. All cloned instances will be allocated
/// with the provided allocator.
template<std::derived_from<SyntaxNode> T>
T* deepClone(const T& node, BumpAllocator& alloc) {
    return static_cast<T*>(deepClone(static_cast<const SyntaxNode&>(node), alloc));
}

/// Represents a source range or a way to get one by materializing
/// it from a syntax node. This exists to avoid computing the source
/// range of a node unless it's actually needed.
class DeferredSourceRange {
public:
    DeferredSourceRange() = default;
    DeferredSourceRange(SourceRange range) : range(range), node(nullptr, true) {}
    DeferredSourceRange(const SyntaxNode& node) : node(&node, false) {}
    DeferredSourceRange(const SyntaxNode& node, SourceRange range) :
        range(range), node(&node, true) {}

    SourceRange get() const {
        if (!node.getInt()) {
            if (auto ptr = node.getPointer())
                range = ptr->sourceRange();
            node.setInt(true);
        }
        return range;
    }

    SourceRange operator*() const { return get(); }

    const SyntaxNode* syntax() const { return node.getPointer(); }

private:
    mutable SourceRange range;
    mutable PointerIntPair<const SyntaxNode*, 1, 1, bool> node;
};

/// Common base for the three syntax-list container types.
template<typename Derived, typename Element>
class SyntaxListBase {
public:
    SyntaxListBase() = default;
    SyntaxListBase(nullptr_t) {}

    /// @return true if the list is empty, false otherwise.
    [[nodiscard]] bool empty() const noexcept { return raw_ == 0; }

protected:
    static constexpr uintptr_t TagMask = 0x3;

    /// @return the encoding tag for a non-empty list.
    [[nodiscard]] uintptr_t tag() const noexcept { return raw_ & TagMask; }

    /// @return the masked-off pointer bits (only meaningful when raw_ != 0).
    [[nodiscard]] uintptr_t rawPtrBits() const noexcept { return raw_ & ~TagMask; }

    /// @return the size encoded in the header preceding the storage at
    /// @a ptrBits. The caller must ensure that @a ptrBits actually points
    /// at a headered block.
    [[nodiscard]] static size_t headeredSize(uintptr_t ptrBits) noexcept {
        return *(reinterpret_cast<const size_t*>(ptrBits) - 1);
    }

    /// Allocates a contiguous block of @a count elements (no header) and
    /// returns the resulting (untagged) raw pointer.
    static uintptr_t allocateContiguous(BumpAllocator& alloc, std::span<const Element> elements) {
        SLANG_ASSERT(!elements.empty());
        const size_t n = elements.size();
        std::byte* mem = alloc.allocate(n * sizeof(Element), alignof(Element));
        Element* dest = reinterpret_cast<Element*>(mem);
        std::ranges::uninitialized_copy(elements.begin(), elements.end(), dest, dest + n);
        return reinterpret_cast<uintptr_t>(dest);
    }

    /// Allocates a `[size_t header][N elements]` block and returns the
    /// resulting (untagged) raw pointer to the elements.
    static uintptr_t allocateHeadered(BumpAllocator& alloc, std::span<const Element> elements) {
        SLANG_ASSERT(!elements.empty());

        // The size header lives in the size_t-sized slot immediately before `dest`.
        // When alignof(Element) exceeds sizeof(size_t) (e.g. 8-byte Token alignment on
        // WASM where size_t is 4 bytes), pad the prefix up to alignof(Element) so the
        // returned pointer remains correctly aligned for Element while still leaving a
        // size_t-aligned header slot at `dest - 1`.
        constexpr size_t headerSize = sizeof(size_t);
        constexpr size_t prefix = std::max(headerSize, alignof(Element));
        constexpr size_t allocAlign = std::max(alignof(Element), alignof(size_t));

        const size_t len = elements.size();
        const size_t bytes = prefix + len * sizeof(Element);
        std::byte* mem = alloc.allocate(bytes, allocAlign);
        Element* dest = reinterpret_cast<Element*>(mem + prefix);
        *(reinterpret_cast<size_t*>(dest) - 1) = len;
        std::ranges::uninitialized_copy(elements.begin(), elements.end(), dest, dest + len);
        return reinterpret_cast<uintptr_t>(dest);
    }

    /// All three derived classes (SyntaxList, TokenList, SeparatedSyntaxList)
    /// share the same single-pointer representation: a tagged `uintptr_t` in `raw_`.
    /// The encoding scheme uses the low two bits of `raw_` to distinguish small-list
    /// optimizations from a "headered" allocation of the form `[size_t header][N elements...]`,
    /// where the size lives in the slot just before the data pointer.
    ///
    /// `SyntaxList` exploits the fact that its element type is itself a pointer; a one-element
    /// list stores the single `T*` value directly in `raw_` with no allocation at all, in which
    /// case `&raw_` reinterpreted as `T**` is a valid one-element span/iterator. To keep that
    /// direct encoding tag-free, SyntaxList uses tag `01` for headered and tag `10` for
    /// two-element.The other two list types whose elements aren't pointers keep the simpler
    /// "tag `00` = headered" encoding.
    ///
    /// `raw_ == 0` always means empty (no allocation).
    ///
    /// An empty list costs only `sizeof(void*)`, and small lists save the `size_t` header
    /// allocation. Single-element `SyntaxList<T>` saves any heap allocation entirely.
    uintptr_t raw_ = 0;
};

/// A container of syntax nodes.
template<typename T>
class SLANG_EXPORT SyntaxList : public SyntaxListBase<SyntaxList<T>, T*> {
    // Tag bit meaning:
    //   raw_ == 0             : empty
    //   tag 00 (raw_ != 0)    : 1-element direct
    //   tag TagHeadered (01)  : >= 3 elements, headered allocation
    //   tag TagSmall2 (10)    : 2-element heap (no header)
    static constexpr uintptr_t TagHeadered = 0x1;
    static constexpr uintptr_t TagSmall2 = 0x2;

public:
    using Base = SyntaxListBase<SyntaxList<T>, T*>;
    using value_type = T*;
    using reference = T*&;
    using const_reference = T* const&;
    using pointer = T**;
    using const_pointer = T* const*;
    using iterator = T**;
    using const_iterator = T* const*;
    using size_type = size_t;

    using Base::Base;
    using Base::empty;

    /// Constructs a list by copying the elements of @a src into storage allocated
    /// from @a alloc. The element type of the source range must be `T*`.
    template<std::ranges::contiguous_range R>
        requires std::same_as<std::ranges::range_value_t<R>, T*>
    SyntaxList(BumpAllocator& alloc, const R& src) {
        std::span<T* const> elements(src);
        switch (elements.size()) {
            case 0:
                this->raw_ = 0;
                break;
            case 1:
                this->raw_ = reinterpret_cast<uintptr_t>(elements[0]);
                SLANG_ASSERT((this->raw_ & this->TagMask) == 0);
                break;
            case 2:
                this->raw_ = this->allocateContiguous(alloc, src) | TagSmall2;
                break;
            default:
                this->raw_ = this->allocateHeadered(alloc, src) | TagHeadered;
                break;
        }
    }

    /// Constructs a syntax list from a span of TokenOrSyntax elements.
    /// Every such element must actually be a syntax node of the correct concrete type.
    SyntaxList(BumpAllocator& alloc, std::span<const TokenOrSyntax> children) {
        SmallVector<T*> buffer(children.size(), UninitializedTag());
        for (auto& t : children)
            buffer.push_back(&t.node()->as<T>());
        *this = SyntaxList<T>(alloc, buffer);
    }

    /// @return the number of elements in the list.
    [[nodiscard]] size_t size() const noexcept {
        if (this->raw_ == 0)
            return 0;
        switch (this->tag()) {
            case 0:
                // Direct 1-element encoding.
                return 1;
            case TagHeadered:
                return Base::headeredSize(this->rawPtrBits());
            case TagSmall2:
                return 2;
            default:
                SLANG_UNREACHABLE;
        }
    }

    /// @return a reference to the i-th element.
    const T* operator[](size_t index) const {
        SLANG_ASSERT(index < size());
        return data()[index];
    }
    T*& operator[](size_t index) {
        SLANG_ASSERT(index < size());
        return data()[index];
    }

    const T* front() const {
        SLANG_ASSERT(!empty());
        return (*this)[0];
    }

    const T* back() const {
        SLANG_ASSERT(!empty());
        return (*this)[size() - 1];
    }

    const_iterator begin() const noexcept { return this->empty() ? nullptr : data(); }
    const_iterator end() const noexcept { return this->empty() ? nullptr : data() + size(); }

    /// @return the elements as a `std::span`.
    operator std::span<const T* const>() const noexcept {
        return this->empty() ? std::span<T* const>() : std::span<T* const>(data(), size());
    }

    /// Number of child items the list contributes to its parent's flattened
    /// child index space.
    size_t getChildCount() const { return this->size(); }

    /// Gets the i-th element as a (Const)TokenOrSyntax.
    TokenOrSyntax getChild(size_t index) { return (*this)[index]; }
    ConstTokenOrSyntax getChild(size_t index) const { return (*this)[index]; }
    PtrTokenOrSyntax getChildPtr(size_t index) { return (*this)[index]; }

    /// Replaces the i-th element with @a child.
    void setChild(size_t index, TokenOrSyntax child) {
        T* node = &child.node()->as<T>();
        SLANG_ASSERT((reinterpret_cast<uintptr_t>(node) & this->TagMask) == 0);
        (*this)[index] = node;
    }

    /// Compute the SourceRange spanning all the elements of this list. If
    /// the list is empty, returns an empty default SourceRange.
    SourceRange sourceRange() const {
        if (this->empty())
            return {};

        auto f = this->front()->getFirstToken();
        auto l = this->back()->getLastToken();
        return SourceRange(f.location(), l.location() + l.rawText().length());
    }

private:
    T** data() const noexcept {
        if (this->tag() == 0)
            return reinterpret_cast<T**>(const_cast<uintptr_t*>(&this->raw_));
        return reinterpret_cast<T**>(this->rawPtrBits());
    }
};

template<typename T>
SyntaxList<T>* deepClone(const SyntaxList<T>& node, BumpAllocator& alloc) {
    SmallVector<T*> buffer(node.size(), UninitializedTag());
    for (auto t : node)
        buffer.push_back(deepClone(*t, alloc));

    return alloc.emplace<SyntaxList<T>>(alloc, buffer);
}

/// A container of tokens.
class SLANG_EXPORT TokenList : public SyntaxListBase<TokenList, parsing::Token> {
    // Tag bit meaning:
    //   raw_ == 0          : empty
    //   tag 00 (raw_ != 0) : headered allocation (size in header)
    //   tag TagSmall1 (01) : 1-element heap, no header
    //   tag TagSmall2 (10) : 2-element heap, no header
    static constexpr uintptr_t TagSmall1 = 0x1;
    static constexpr uintptr_t TagSmall2 = 0x2;

public:
    using Token = parsing::Token;
    using Base = SyntaxListBase<TokenList, Token>;
    using value_type = Token;
    using reference = Token&;
    using const_reference = const Token&;
    using pointer = Token*;
    using const_pointer = const Token*;
    using iterator = Token*;
    using const_iterator = const Token*;
    using size_type = size_t;

    using Base::Base;
    using Base::empty;

    /// Constructs a token list by copying the elements of @a src into storage
    /// allocated from @a alloc. The element type of the source range must
    /// be `parsing::Token`.
    template<std::ranges::contiguous_range R>
        requires std::same_as<std::ranges::range_value_t<R>, Token>
    TokenList(BumpAllocator& alloc, const R& src) {
        std::span<const Token> elements(src);
        switch (elements.size()) {
            case 0:
                this->raw_ = 0;
                break;
            case 1:
                this->raw_ = this->allocateContiguous(alloc, src) | TagSmall1;
                break;
            case 2:
                this->raw_ = this->allocateContiguous(alloc, src) | TagSmall2;
                break;
            default:
                this->raw_ = this->allocateHeadered(alloc, src);
                break;
        }
    }

    /// Constructs a token list from a span of TokenOrSyntax elements.
    /// Every such element must actually be a token.
    TokenList(BumpAllocator& alloc, std::span<const TokenOrSyntax> children) {
        SmallVector<Token> buffer(children.size(), UninitializedTag());
        for (auto& t : children)
            buffer.push_back(t.token());
        *this = TokenList(alloc, buffer);
    }

    /// @return the number of elements in the list.
    [[nodiscard]] size_t size() const noexcept {
        if (this->raw_ == 0)
            return 0;
        switch (this->tag()) {
            case 0:
                return Base::headeredSize(this->rawPtrBits());
            case TagSmall1:
                return 1;
            case TagSmall2:
                return 2;
            default:
                SLANG_UNREACHABLE;
        }
    }

    Token& operator[](size_t index) {
        SLANG_ASSERT(index < size());
        return data()[index];
    }
    const Token& operator[](size_t index) const {
        SLANG_ASSERT(index < size());
        return data()[index];
    }

    Token* begin() const noexcept { return data(); }
    Token* end() const noexcept { return data() + size(); }

    Token& front() const {
        SLANG_ASSERT(!empty());
        return data()[0];
    }

    Token& back() const {
        SLANG_ASSERT(!empty());
        return data()[size() - 1];
    }

    /// Number of child items the list contributes to its parent's flattened
    /// child index space.
    size_t getChildCount() const { return this->size(); }

    /// Gets the i-th token as a (Const)TokenOrSyntax.
    TokenOrSyntax getChild(size_t index) { return (*this)[index]; }
    ConstTokenOrSyntax getChild(size_t index) const { return (*this)[index]; }
    PtrTokenOrSyntax getChildPtr(size_t index) { return &(*this)[index]; }

    /// Replaces the i-th token with @a child.
    void setChild(size_t index, TokenOrSyntax child) { (*this)[index] = child.token(); }

    /// Compute the SourceRange spanning all tokens of this list. If empty,
    /// returns a default SourceRange.
    SourceRange sourceRange() const {
        if (empty())
            return {};

        auto f = front();
        auto l = back();
        return SourceRange(f.location(), l.location() + l.rawText().length());
    }

private:
    Token* data() const noexcept { return reinterpret_cast<Token*>(this->rawPtrBits()); }
};

/// @brief A container of token-separated syntax nodes.
///
/// The stored elements alternate between delimiters (such as a
/// comma) and nodes.
template<typename T>
class SLANG_EXPORT SeparatedSyntaxList
    : public SyntaxListBase<SeparatedSyntaxList<T>, TokenOrSyntax> {

    // Tag bit encoding:
    //   raw_ == 0          : empty
    //   tag 00 (raw_ != 0) : 1-element direct
    //   tag TagHeadered    : headered allocation (raw size in header)
    //   tag TagSmall2      : 2 raw elements heap, no header
    static constexpr uintptr_t TagHeadered = 0x1;
    static constexpr uintptr_t TagSmall2 = 0x2;

public:
    using Base = SyntaxListBase<SeparatedSyntaxList<T>, TokenOrSyntax>;

    /// An iterator that will iterate over just the nodes (and skip the delimiters) in the
    /// parent SeparatedSyntaxList.
    template<typename U>
    class iterator_base : public iterator_facade<iterator_base<U>> {
    public:
        using ParentList = std::conditional_t<std::is_const_v<std::remove_pointer_t<U>>,
                                              const SeparatedSyntaxList, SeparatedSyntaxList>;

        iterator_base() : list(nullptr), index(0) {}
        iterator_base(ParentList& list, size_t index) : list(&list), index(index) {}

        U dereference() const { return (*list)[index]; }

        bool equals(const iterator_base& other) const {
            return list == other.list && index == other.index;
        }

        ptrdiff_t distance_to(const iterator_base& other) const {
            return ptrdiff_t(other.index) - ptrdiff_t(index);
        }

        void advance(ptrdiff_t n) { index = size_t(ptrdiff_t(index) + n); }

    private:
        ParentList* list;
        size_t index;
    };

    using iterator = iterator_base<T*>;
    using const_iterator = iterator_base<const T*>;

    using Base::Base;
    using Base::empty;

    /// Constructs a separated list by copying the elements of @a src into
    /// storage allocated from @a alloc. The element type of the source range
    /// must be `TokenOrSyntax`.
    template<std::ranges::contiguous_range R>
        requires std::same_as<std::ranges::range_value_t<R>, TokenOrSyntax>
    SeparatedSyntaxList(BumpAllocator& alloc, const R& src) {
        std::span<const TokenOrSyntax> elements(src);
        switch (elements.size()) {
            case 0:
                this->raw_ = 0;
                break;
            case 1: {
                // Direct: raw_ stores the single T* value verbatim.
                // A 1-element separated list always holds a node (no
                // trailing separator), so this is unambiguous.
                T* node = &elements[0].node()->template as<T>();
                this->raw_ = reinterpret_cast<uintptr_t>(node);
                SLANG_ASSERT((this->raw_ & this->TagMask) == 0);
                break;
            }
            case 2:
                this->raw_ = this->allocateContiguous(alloc, src) | TagSmall2;
                break;
            default:
                this->raw_ = this->allocateHeadered(alloc, src) | TagHeadered;
                break;
        }
    }

    /// Number of items the list contributes to its parent's flattened
    /// child index space (includes interleaved separators).
    size_t getChildCount() const { return rawSize(); }

    /// Gets the i-th item (token or node) from the underlying interleaved span.
    TokenOrSyntax getChild(size_t index) { return rawElem(index); }
    ConstTokenOrSyntax getChild(size_t index) const { return rawElem(index); }
    PtrTokenOrSyntax getChildPtr(size_t index) {
        if (this->tag() == 0) {
            // Direct 1-element encoding: raw_ holds a node pointer.
            SLANG_ASSERT(index == 0);
            return reinterpret_cast<SyntaxNode*>(this->raw_);
        }
        TokenOrSyntax* slot = &rawElemsPtr()[index];
        if (slot->isNode())
            return slot->node();
        else
            return slot->tokenPtr();
    }

    /// Replaces the i-th item with @a child.
    void setChild(size_t index, TokenOrSyntax child) {
        if (this->tag() == 0) {
            SLANG_ASSERT(index == 0);
            SLANG_ASSERT(child.isNode());
            T* node = &child.node()->template as<T>();
            SLANG_ASSERT((reinterpret_cast<uintptr_t>(node) & this->TagMask) == 0);
            this->raw_ = reinterpret_cast<uintptr_t>(node);
            return;
        }
        rawElemsPtr()[index] = child;
    }

    /// Compute the SourceRange spanning all elements of this list. If empty,
    /// returns a default SourceRange.
    SourceRange sourceRange() const {
        if (empty())
            return {};

        auto firstRange = rawElem(0).range();
        auto lastRange = rawElem(rawSize() - 1).range();
        return SourceRange(firstRange.start(), lastRange.end());
    }

    /// @return the number of nodes in the list (doesn't include delimiter tokens in the count).
    [[nodiscard]] size_t size() const noexcept { return (rawSize() + 1) / 2; }

    const T* operator[](size_t index) const {
        if (this->tag() == 0) {
            SLANG_ASSERT(index == 0);
            return reinterpret_cast<const T*>(this->raw_);
        }
        return &rawElemsPtr()[index << 1].node()->template as<T>();
    }

    T* operator[](size_t index) {
        if (this->tag() == 0) {
            SLANG_ASSERT(index == 0);
            return reinterpret_cast<T*>(this->raw_);
        }
        return &rawElemsPtr()[index << 1].node()->template as<T>();
    }

    iterator begin() { return iterator(*this, 0); }
    iterator end() { return iterator(*this, size()); }
    const_iterator begin() const { return cbegin(); }
    const_iterator end() const { return cend(); }
    const_iterator cbegin() const { return const_iterator(*this, 0); }
    const_iterator cend() const { return const_iterator(*this, size()); }

private:
    size_t rawSize() const noexcept {
        if (this->raw_ == 0)
            return 0;
        switch (this->tag()) {
            case 0:
                // Direct 1-element encoding.
                return 1;
            case TagHeadered:
                return Base::headeredSize(this->rawPtrBits());
            case TagSmall2:
                return 2;
            default:
                SLANG_UNREACHABLE;
        }
    }

    TokenOrSyntax rawElem(size_t index) const noexcept {
        if (this->tag() == 0) {
            // Direct 1-element encoding: raw_ holds a node pointer.
            SLANG_ASSERT(index == 0);
            return TokenOrSyntax(reinterpret_cast<SyntaxNode*>(this->raw_));
        }
        return rawElemsPtr()[index];
    }

    TokenOrSyntax* rawElemsPtr() const noexcept {
        SLANG_ASSERT(this->tag() != 0);
        return reinterpret_cast<TokenOrSyntax*>(this->rawPtrBits());
    }
};

template<typename T>
SeparatedSyntaxList<T>* deepClone(const SeparatedSyntaxList<T>& node, BumpAllocator& alloc) {
    SmallVector<TokenOrSyntax> buffer(node.size(), UninitializedTag());
    for (size_t i = 0, count = node.getChildCount(); i < count; i++) {
        auto ele = node.getChild(i);
        if (ele.isToken())
            buffer.push_back(ele.token().deepClone(alloc));
        else
            buffer.push_back(static_cast<T*>(deepClone(*ele.node(), alloc)));
    }
    return alloc.emplace<SeparatedSyntaxList<T>>(alloc, buffer);
}

inline TokenList* deepClone(const TokenList& node, BumpAllocator& alloc) {
    SmallVector<parsing::Token> buffer(node.size(), UninitializedTag());
    for (const auto& ele : node) {
        buffer.push_back(ele.deepClone(alloc));
    }
    return alloc.emplace<TokenList>(alloc, buffer);
}

/// Type trait that is true for the three syntax-list container types
/// (`SyntaxList<T>`, `TokenList`, `SeparatedSyntaxList<T>`).
template<typename T>
struct is_syntax_list : std::false_type {};

template<typename T>
struct is_syntax_list<SyntaxList<T>> : std::true_type {};

template<>
struct is_syntax_list<TokenList> : std::true_type {};

template<typename T>
struct is_syntax_list<SeparatedSyntaxList<T>> : std::true_type {};

template<typename T>
inline constexpr bool is_syntax_list_v = is_syntax_list<T>::value;

} // namespace slang::syntax
