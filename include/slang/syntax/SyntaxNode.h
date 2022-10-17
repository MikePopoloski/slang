//------------------------------------------------------------------------------
//! @file SyntaxNode.h
//! @brief Base class and utilities for syntax nodes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string>
#include <variant>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxKind.h"
#include "slang/util/Iterator.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang::syntax {

class SyntaxNode;

/// A token or a constant syntax node.
struct SLANG_EXPORT ConstTokenOrSyntax : public std::variant<parsing::Token, const SyntaxNode*> {
    using Base = std::variant<parsing::Token, const SyntaxNode*>;
    ConstTokenOrSyntax(parsing::Token token) : Base(token) {}
    ConstTokenOrSyntax(const SyntaxNode* node) : Base(node) {}
    ConstTokenOrSyntax(nullptr_t) : Base(parsing::Token()) {}

    /// @return true if the object is a token.
    bool isToken() const { return this->index() == 0; }

    /// @return true if the object is a syntax node.
    bool isNode() const { return this->index() == 1; }

    /// Gets access to the object as a token (throwing an exception
    /// if it's not actually a token).
    parsing::Token token() const { return std::get<0>(*this); }

    /// Gets access to the object as a syntax node (throwing an exception
    /// if it's not actually a syntax node).
    const SyntaxNode* node() const { return std::get<1>(*this); }
};

/// A token or a syntax node.
struct SLANG_EXPORT TokenOrSyntax : public ConstTokenOrSyntax {
    TokenOrSyntax(parsing::Token token) : ConstTokenOrSyntax(token) {}
    TokenOrSyntax(SyntaxNode* node) : ConstTokenOrSyntax(node) {}
    TokenOrSyntax(nullptr_t) : ConstTokenOrSyntax(parsing::Token()) {}

    /// Gets access to the object as a syntax node (throwing an exception
    /// if it's not actually a syntax node).
    SyntaxNode* node() const {
        // const_cast is safe because we only could have constructed this
        // object with a non-const pointer.
        return const_cast<SyntaxNode*>(std::get<1>(*this));
    }
};

/// Base class for all syntax nodes.
class SLANG_EXPORT SyntaxNode {
public:
    using Token = parsing::Token;

    /// The parent node of this syntax node. The root of the syntax
    /// tree does not have a parent (will be nullptr).
    SyntaxNode* parent = nullptr;

    /// The kind of syntax node.
    SyntaxKind kind;

    /// Print the node and all of its children to a string.
    std::string toString() const;

    /// Get the first leaf token in this subtree.
    Token getFirstToken() const;

    /// Get the last leaf token in this subtree.
    Token getLastToken() const;

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

    /// Gets the number of (direct) children underneath this node in the tree.
    size_t getChildCount() const; // Note: implemented in AllSyntax.cpp

    /// Reinterprets this node as being of type T. In debug this will assert
    /// that the dynamic kind is appropriate for the specified static type.
    template<typename T>
    T& as() {
        ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    /// Reinterprets this node as being of type T. In debug this will assert
    /// that the dynamic kind is appropriate for the specified static type.
    template<typename T>
    const T& as() const {
        ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    /// Applies a visitor object to this node by dispatching based on the
    /// dynamic kind. The given @a args are forwarded to the visitor.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args);

    /// Applies a visitor object to this node by dispatching based on the
    /// dynamic kind. The given @a args are forwarded to the visitor.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

    /// A base implemention of the method that checks correctness of dynamic casting.
    /// Derived nodes should reimplement this and return true if the provided syntax kind
    /// is compatible with the static type of the object.
    static bool isKind(SyntaxKind) { return true; }

protected:
    explicit SyntaxNode(SyntaxKind kind) : kind(kind) {}

private:
    ConstTokenOrSyntax getChild(size_t index) const;
    TokenOrSyntax getChild(size_t index);
};

SLANG_EXPORT SyntaxNode* clone(const SyntaxNode&, BumpAllocator&);
SLANG_EXPORT SyntaxNode* deepClone(const SyntaxNode&, BumpAllocator&);

template<typename T, typename = std::enable_if_t<std::is_base_of_v<SyntaxNode, T>>>
T* clone(const T& node, BumpAllocator& alloc) {
    return static_cast<T*>(clone(static_cast<const SyntaxNode&>(node), alloc));
}

template<typename T, typename = std::enable_if_t<std::is_base_of_v<SyntaxNode, T>>>
T* deepClone(const T& node, BumpAllocator& alloc) {
    return static_cast<T*>(deepClone(static_cast<const SyntaxNode&>(node), alloc));
}

/// A base class for syntax nodes that represent a list of items.
class SLANG_EXPORT SyntaxListBase : public SyntaxNode {
public:
    /// Gets the number of child items in the node.
    size_t getChildCount() const { return childCount; }

    /// Gets the child (token or node) at the given index.
    virtual TokenOrSyntax getChild(size_t index) = 0;

    /// Gets the child (token or node) at the given index.
    virtual ConstTokenOrSyntax getChild(size_t index) const = 0;

    /// Sets the child (token or node) at the given index.
    virtual void setChild(size_t index, TokenOrSyntax child) = 0;

    /// Clones the list into a new node using the provided allocator.
    virtual SyntaxListBase* clone(BumpAllocator& alloc) const = 0;

    /// Overwrites all children with the new set of provided @a children (and making
    /// a copy with the provided allocator).
    virtual void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) = 0;

    static bool isKind(SyntaxKind kind);

protected:
    SyntaxListBase(SyntaxKind kind, size_t childCount) : SyntaxNode(kind), childCount(childCount) {}

    size_t childCount;
};

/// A syntax node that represents a list of child syntax nodes.
template<typename T>
class SLANG_EXPORT SyntaxList : public SyntaxListBase, public span<T*> {
public:
    SyntaxList(nullptr_t) : SyntaxList(span<T*>()) {}
    SyntaxList(span<T*> elements) :
        SyntaxListBase(SyntaxKind::SyntaxList, elements.size()), span<T*>(elements) {}

    // TODO: this is here to work around a bug in GCC 9
    operator span<const T* const>() const {
        return span<const T* const>(this->data(), this->size());
    }

private:
    TokenOrSyntax getChild(size_t index) final { return (*this)[index]; }
    ConstTokenOrSyntax getChild(size_t index) const final { return (*this)[index]; }

    void setChild(size_t index, TokenOrSyntax child) final {
        (*this)[index] = &child.node()->as<T>();
    }

    SyntaxListBase* clone(BumpAllocator& alloc) const final {
        return alloc.emplace<SyntaxList<T>>(*this);
    }

    void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) final {
        SmallVector<T*> buffer(children.size(), UninitializedTag());
        for (auto& t : children)
            buffer.push_back(&t.node()->as<T>());

        *this = buffer.copy(alloc);
        childCount = buffer.size();
    }
};

template<typename T>
SyntaxList<T>* deepClone(const SyntaxList<T>& node, BumpAllocator& alloc) {
    SmallVector<T*> buffer(node.size(), UninitializedTag());
    for (auto& t : node)
        buffer.push_back(deepClone(*t, alloc));

    return alloc.emplace<SyntaxList<T>>(buffer.copy(alloc));
}

/// A syntax node that represents a list of child tokens.
class SLANG_EXPORT TokenList : public SyntaxListBase, public span<parsing::Token> {
public:
    TokenList(nullptr_t) : TokenList(span<Token>()) {}
    TokenList(span<Token> elements) :
        SyntaxListBase(SyntaxKind::TokenList, elements.size()), span<Token>(elements) {}

private:
    TokenOrSyntax getChild(size_t index) final { return (*this)[index]; }
    ConstTokenOrSyntax getChild(size_t index) const final { return (*this)[index]; }
    void setChild(size_t index, TokenOrSyntax child) final { (*this)[index] = child.token(); }

    SyntaxListBase* clone(BumpAllocator& alloc) const final {
        return alloc.emplace<TokenList>(*this);
    }

    void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) final {
        SmallVector<Token> buffer(children.size(), UninitializedTag());
        for (auto& t : children)
            buffer.push_back(t.token());

        *this = buffer.copy(alloc);
        childCount = buffer.size();
    }
};

/// A syntax node that represents a token-separated list of child syntax nodes.
/// The stored children are assumed to alternate between delimiters (such as a comma) and nodes.
template<typename T>
class SLANG_EXPORT SeparatedSyntaxList : public SyntaxListBase {
public:
    /// An iterator that will iterate over just the nodes (and skip the delimiters) in the
    /// parent SeparatedSyntaxList.
    template<typename U>
    class iterator_base
        : public iterator_facade<iterator_base<U>, std::random_access_iterator_tag, U, size_t> {
    public:
        using ParentList = std::conditional_t<std::is_const_v<std::remove_pointer_t<U>>,
                                              const SeparatedSyntaxList, SeparatedSyntaxList>;
        iterator_base(ParentList& list, size_t index) : list(&list), index(index) {}
        iterator_base(const iterator_base& other) = default;

        iterator_base& operator=(const iterator_base& other) = default;

        bool operator==(const iterator_base& other) const {
            return list == other.list && index == other.index;
        }

        bool operator<(const iterator_base& other) const { return index < other.index; }

        U operator*() const { return (*list)[index]; }

        size_t operator-(const iterator_base& other) const { return index - other.index; }

        iterator_base& operator+=(ptrdiff_t n) {
            index = size_t(ptrdiff_t(index) + n);
            return *this;
        }
        iterator_base& operator-=(ptrdiff_t n) {
            index = size_t(ptrdiff_t(index) - n);
            return *this;
        }

    private:
        ParentList* list;
        size_t index;
    };

    using iterator = iterator_base<T*>;
    using const_iterator = iterator_base<const T*>;

    SeparatedSyntaxList(nullptr_t) : SeparatedSyntaxList(span<TokenOrSyntax>()) {}
    SeparatedSyntaxList(span<TokenOrSyntax> elements) :
        SyntaxListBase(SyntaxKind::SeparatedList, elements.size()), elements(elements) {}

    /// @return the elements of nodes in the list
    [[nodiscard]] span<const ConstTokenOrSyntax> elems() const {
        return span<const ConstTokenOrSyntax>(elements.data(), elements.size());
    }

    /// @return the elements of nodes in the list
    [[nodiscard]] span<TokenOrSyntax> elems() { return elements; }

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
    TokenOrSyntax getChild(size_t index) final { return elements[index]; }
    ConstTokenOrSyntax getChild(size_t index) const final { return elements[index]; }
    void setChild(size_t index, TokenOrSyntax child) final { elements[index] = child; }

    SyntaxListBase* clone(BumpAllocator& alloc) const final {
        return alloc.emplace<SeparatedSyntaxList<T>>(*this);
    }

    void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) final {
        SmallVector<TokenOrSyntax> buffer(children.size(), UninitializedTag());
        buffer.append(children);

        elements = buffer.copy(alloc);
        childCount = buffer.size();
    }

    span<TokenOrSyntax> elements;
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

} // namespace slang::syntax
