//------------------------------------------------------------------------------
//! @file SyntaxNode.h
//! @brief Base class and utilities for syntax nodes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cstring>
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

/// A container of syntax nodes.
template<typename T>
class SLANG_EXPORT SyntaxList : public std::span<T*> {
public:
    SyntaxList(nullptr_t) : SyntaxList(std::span<T*>()) {}
    SyntaxList(std::span<T*> elements) : std::span<T*>(elements) {}

    /// Number of child items the list contributes to its parent's flattened
    /// child index space.
    size_t getChildCount() const { return this->size(); }

    /// Gets the i-th element as a (Const)TokenOrSyntax.
    TokenOrSyntax getChild(size_t index) { return (*this)[index]; }
    ConstTokenOrSyntax getChild(size_t index) const { return (*this)[index]; }
    PtrTokenOrSyntax getChildPtr(size_t index) { return (*this)[index]; }

    /// Replaces the i-th element with @a child.
    void setChild(size_t index, TokenOrSyntax child) { (*this)[index] = &child.node()->as<T>(); }

    /// Replaces the entire span with the provided @a children, copying the
    /// resulting buffer into @a alloc.
    void resetAll(BumpAllocator& alloc, std::span<const TokenOrSyntax> children) {
        SmallVector<T*> buffer(children.size(), UninitializedTag());
        for (auto& t : children)
            buffer.push_back(&t.node()->as<T>());

        *this = buffer.copy(alloc);
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
};

template<typename T>
SyntaxList<T>* deepClone(const SyntaxList<T>& node, BumpAllocator& alloc) {
    SmallVector<T*> buffer(node.size(), UninitializedTag());
    for (auto t : node)
        buffer.push_back(deepClone(*t, alloc));

    return alloc.emplace<SyntaxList<T>>(buffer.copy(alloc));
}

/// A container of tokens.
class SLANG_EXPORT TokenList : public std::span<parsing::Token> {
public:
    TokenList(nullptr_t) : TokenList(std::span<parsing::Token>()) {}
    TokenList(std::span<parsing::Token> elements) : std::span<parsing::Token>(elements) {}

    /// Number of child items the list contributes to its parent's flattened
    /// child index space.
    size_t getChildCount() const { return this->size(); }

    /// Gets the i-th token as a (Const)TokenOrSyntax.
    TokenOrSyntax getChild(size_t index) { return (*this)[index]; }
    ConstTokenOrSyntax getChild(size_t index) const { return (*this)[index]; }
    PtrTokenOrSyntax getChildPtr(size_t index) { return &(*this)[index]; }

    /// Replaces the i-th token with @a child.
    void setChild(size_t index, TokenOrSyntax child) { (*this)[index] = child.token(); }

    /// Replaces the entire span with the provided @a children, copying the
    /// resulting buffer into @a alloc.
    void resetAll(BumpAllocator& alloc, std::span<const TokenOrSyntax> children) {
        SmallVector<parsing::Token> buffer(children.size(), UninitializedTag());
        for (auto& t : children)
            buffer.push_back(t.token());

        *this = buffer.copy(alloc);
    }

    /// Compute the SourceRange spanning all tokens of this list. If empty,
    /// returns a default SourceRange.
    SourceRange sourceRange() const {
        if (empty())
            return {};

        auto f = front();
        auto l = back();
        return SourceRange(f.location(), l.location() + l.rawText().length());
    }
};

/// @brief A container of token-separated syntax nodes.
///
/// The stored elements alternate between delimiters (such as a
/// comma) and nodes. Unlike SyntaxList, the elements span includes the
/// separators interleaved with the nodes.
template<typename T>
class SLANG_EXPORT SeparatedSyntaxList {
public:
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

    SeparatedSyntaxList(nullptr_t) : SeparatedSyntaxList(std::span<TokenOrSyntax>()) {}
    SeparatedSyntaxList(std::span<TokenOrSyntax> elements) : elements(elements) {}

    /// Number of items the list contributes to its parent's flattened
    /// child index space (includes interleaved separators).
    size_t getChildCount() const { return elements.size(); }

    /// Gets the i-th item (token or node) from the underlying interleaved span.
    TokenOrSyntax getChild(size_t index) { return elements[index]; }
    ConstTokenOrSyntax getChild(size_t index) const { return elements[index]; }
    PtrTokenOrSyntax getChildPtr(size_t index) {
        if (elements[index].isNode())
            return elements[index].node();
        else
            return elements[index].tokenPtr();
    }

    /// Replaces the i-th item with @a child.
    void setChild(size_t index, TokenOrSyntax child) { elements[index] = child; }

    /// Replaces the entire span with the provided @a children, copying the
    /// resulting buffer into @a alloc.
    void resetAll(BumpAllocator& alloc, std::span<const TokenOrSyntax> children) {
        SmallVector<TokenOrSyntax> buffer(children.size(), UninitializedTag());
        buffer.append_range(children);

        elements = buffer.copy(alloc);
    }

    /// Compute the SourceRange spanning all elements of this list. If empty,
    /// returns a default SourceRange.
    SourceRange sourceRange() const {
        if (elements.empty())
            return {};

        auto firstRange = elements.front().range();
        auto lastRange = elements.back().range();
        return SourceRange(firstRange.start(), lastRange.end());
    }

    /// @return the elements of nodes in the list
    [[nodiscard]] std::span<const ConstTokenOrSyntax> elems() const {
        return std::span<const ConstTokenOrSyntax>(
            static_cast<ConstTokenOrSyntax*>(elements.data()), elements.size());
    }

    /// @return the elements of nodes in the list
    [[nodiscard]] std::span<TokenOrSyntax> elems() { return elements; }

    /// @return true if the list is empty, and false if it has elements.
    [[nodiscard]] bool empty() const { return elements.empty(); }

    /// @return the number of nodes in the list (doesn't include delimiter tokens in the count).
    [[nodiscard]] size_t size() const noexcept { return (elements.size() + 1) / 2; }

    const T* operator[](size_t index) const {
        index <<= 1;
        return &elements[index].node()->template as<T>();
    }

    T* operator[](size_t index) {
        index <<= 1;
        return &elements[index].node()->template as<T>();
    }

    iterator begin() { return iterator(*this, 0); }
    iterator end() { return iterator(*this, size()); }
    const_iterator begin() const { return cbegin(); }
    const_iterator end() const { return cend(); }
    const_iterator cbegin() const { return const_iterator(*this, 0); }
    const_iterator cend() const { return const_iterator(*this, size()); }

private:
    std::span<TokenOrSyntax> elements;
};

template<typename T>
SeparatedSyntaxList<T>* deepClone(const SeparatedSyntaxList<T>& node, BumpAllocator& alloc) {
    SmallVector<TokenOrSyntax> buffer(node.size(), UninitializedTag());
    for (const auto& ele : node.elems()) {
        if (ele.isToken())
            buffer.push_back(ele.token().deepClone(alloc));
        else
            buffer.push_back(static_cast<T*>(deepClone(*ele.node(), alloc)));
    }
    return alloc.emplace<SeparatedSyntaxList<T>>(buffer.copy(alloc));
}

inline TokenList* deepClone(const TokenList& node, BumpAllocator& alloc) {
    SmallVector<parsing::Token> buffer(node.size(), UninitializedTag());
    for (const auto& ele : node) {
        buffer.push_back(ele.deepClone(alloc));
    }
    return alloc.emplace<TokenList>(buffer.copy(alloc));
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
