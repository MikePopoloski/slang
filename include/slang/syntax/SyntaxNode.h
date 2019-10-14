//------------------------------------------------------------------------------
// SyntaxNode.h
// Base class and utilities for syntax nodes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <string>
#include <variant>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxKind.h"
#include "slang/util/Iterator.h"
#include "slang/util/SmallVector.h"

namespace slang {

class SyntaxNode;
struct DataTypeSyntax;

enum class TokenKind : uint16_t;

string_view getSimpleTypeName(const DataTypeSyntax& syntax);

SyntaxKind getUnaryPrefixExpression(TokenKind kind);
SyntaxKind getUnaryPostfixExpression(TokenKind kind);
SyntaxKind getLiteralExpression(TokenKind kind);
SyntaxKind getBinaryExpression(TokenKind kind);
SyntaxKind getKeywordNameExpression(TokenKind kind);
SyntaxKind getIntegerType(TokenKind kind);
SyntaxKind getKeywordType(TokenKind kind);
SyntaxKind getProceduralBlockKind(TokenKind kind);
SyntaxKind getModuleDeclarationKind(TokenKind kind);
SyntaxKind getModuleHeaderKind(TokenKind kind);
TokenKind getModuleEndKind(TokenKind kind);
int getPrecedence(SyntaxKind kind);
bool isSpecialMethodName(SyntaxKind kind);
bool isRightAssociative(SyntaxKind kind);
bool isPossibleDataType(TokenKind kind);
bool isPossibleExpression(TokenKind kind);
bool isPossibleStatement(TokenKind kind);
bool isNetType(TokenKind kind);
bool isPortDirection(TokenKind kind);
bool isPossibleArgument(TokenKind kind);
bool isComma(TokenKind kind);
bool isSemicolon(TokenKind kind);
bool isCloseBrace(TokenKind kind);
bool isIdentifierOrComma(TokenKind kind);
bool isPossibleExpressionOrComma(TokenKind kind);
bool isPossibleExpressionOrCommaOrDefault(TokenKind kind);
bool isPossibleExpressionOrTripleAnd(TokenKind kind);
bool isPossibleForInitializer(TokenKind kind);
bool isPossibleOpenRangeElement(TokenKind kind);
bool isPossiblePattern(TokenKind kind);
bool isPossibleDelayOrEventControl(TokenKind kind);
bool isEndKeyword(TokenKind kind);
bool isDeclarationModifier(TokenKind kind);
bool isMemberQualifier(TokenKind kind);
bool isEndOfParenList(TokenKind kind);
bool isEndOfBracedList(TokenKind kind);
bool isEndOfBracketedList(TokenKind kind);
bool isEndOfCaseItem(TokenKind kind);
bool isEndOfConditionalPredicate(TokenKind kind);
bool isEndOfAttribute(TokenKind kind);
bool isEndOfParameterList(TokenKind kind);
bool isEndOfTransSet(TokenKind kind);
bool isNotInType(TokenKind kind);
bool isNotInPortReference(TokenKind kind);
bool isNotInConcatenationExpr(TokenKind kind);
bool isNotInParameterList(TokenKind kind);
bool isPossiblePropertyPortItem(TokenKind kind);
bool isPossibleAnsiPort(TokenKind kind);
bool isPossibleNonAnsiPort(TokenKind kind);
bool isPossibleModportPort(TokenKind kind);
bool isPossibleFunctionPort(TokenKind kind);
bool isPossibleParameter(TokenKind kind);
bool isPossiblePortConnection(TokenKind kind);
bool isPossibleVectorDigit(TokenKind kind);
bool isPossibleLetPortItem(TokenKind kind);
bool isPossibleTransSet(TokenKind kind);
bool isBeforeOrSemicolon(TokenKind kind);

template<typename TNode>
struct TokenOrSyntaxBase : public std::variant<Token, TNode> {
    using Base = std::variant<Token, TNode>;
    TokenOrSyntaxBase(Token token) : Base(token) {}
    TokenOrSyntaxBase(TNode node) : Base(node) {}
    TokenOrSyntaxBase(nullptr_t) : Base(Token()) {}

    bool isToken() const { return this->index() == 0; }
    bool isNode() const { return this->index() == 1; }

    Token token() const { return std::get<0>(*this); }
    TNode node() const { return std::get<1>(*this); }

protected:
    TokenOrSyntaxBase() = default;
};

struct TokenOrSyntax : public TokenOrSyntaxBase<SyntaxNode*> {
    using TokenOrSyntaxBase::TokenOrSyntaxBase;
};

struct ConstTokenOrSyntax : public TokenOrSyntaxBase<const SyntaxNode*> {
    using TokenOrSyntaxBase::TokenOrSyntaxBase;

    ConstTokenOrSyntax(TokenOrSyntax tos);
};

/// Base class for all syntax nodes.
class SyntaxNode {
public:
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
    Token childToken(size_t index) const;

    size_t getChildCount() const; // Note: implemented in AllSyntax.cpp

    template<typename T>
    T& as() {
        ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args);

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

    static bool isKind(SyntaxKind) { return true; }

protected:
    explicit SyntaxNode(SyntaxKind kind) : kind(kind) {}

private:
    ConstTokenOrSyntax getChild(size_t index) const;
};

class SyntaxListBase : public SyntaxNode {
public:
    size_t getChildCount() const { return childCount; }

    virtual TokenOrSyntax getChild(size_t index) = 0;
    virtual ConstTokenOrSyntax getChild(size_t index) const = 0;
    virtual void setChild(size_t index, TokenOrSyntax child) = 0;

    virtual SyntaxListBase* clone(BumpAllocator& alloc) const = 0;

    virtual void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) = 0;

    static bool isKind(SyntaxKind kind);

protected:
    SyntaxListBase(SyntaxKind kind, size_t childCount) : SyntaxNode(kind), childCount(childCount) {}

    size_t childCount;
};

template<typename T>
class SyntaxList : public SyntaxListBase, public span<T*> {
public:
    SyntaxList(nullptr_t) : SyntaxList(span<T*>()) {}
    SyntaxList(span<T*> elements);

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
        SmallVectorSized<T*, 8> buffer(children.size());
        for (auto& t : children)
            buffer.append(&t.node()->as<T>());

        *this = buffer.copy(alloc);
        childCount = buffer.size();
    }
};

class TokenList : public SyntaxListBase, public span<Token> {
public:
    TokenList(nullptr_t) : TokenList(span<Token>()) {}
    TokenList(span<Token> elements);

private:
    TokenOrSyntax getChild(size_t index) final { return (*this)[index]; }
    ConstTokenOrSyntax getChild(size_t index) const final { return (*this)[index]; }
    void setChild(size_t index, TokenOrSyntax child) final { (*this)[index] = child.token(); }

    SyntaxListBase* clone(BumpAllocator& alloc) const final {
        return alloc.emplace<TokenList>(*this);
    }

    void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) final {
        SmallVectorSized<Token, 8> buffer(children.size());
        for (auto& t : children)
            buffer.append(t.token());

        *this = buffer.copy(alloc);
        childCount = buffer.size();
    }
};

template<typename T>
class SeparatedSyntaxList : public SyntaxListBase {
public:
    template<typename U>
    class iterator_base
        : public iterator_facade<iterator_base<U>, std::random_access_iterator_tag, U, size_t> {
    public:
        using ParentList = std::conditional_t<std::is_const_v<std::remove_pointer_t<U>>,
                                              const SeparatedSyntaxList, SeparatedSyntaxList>;
        iterator_base(ParentList& list, size_t index) : list(list), index(index) {}

        bool operator==(const iterator_base& other) const {
            return &list == &other.list && index == other.index;
        }

        bool operator<(const iterator_base& other) const { return index < other.index; }

        U operator*() const { return list[index]; }

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
        ParentList& list;
        size_t index;
    };

    using iterator = iterator_base<T*>;
    using const_iterator = iterator_base<const T*>;

    SeparatedSyntaxList(nullptr_t) : SeparatedSyntaxList(span<TokenOrSyntax>()) {}
    SeparatedSyntaxList(span<TokenOrSyntax> elements);

    bool empty() const { return elements.empty(); }
    size_t size() const noexcept { return (elements.size() + 1) / 2; }

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
        SmallVectorSized<TokenOrSyntax, 8> buffer(children.size());
        buffer.appendRange(children);

        elements = buffer.copy(alloc);
        childCount = buffer.size();
    }

    span<TokenOrSyntax> elements;
};

template<typename T>
SyntaxList<T>::SyntaxList(span<T*> elements) :
    SyntaxListBase(SyntaxKind::SyntaxList, elements.size()), span<T*>(elements) {
}

inline TokenList::TokenList(span<Token> elements) :
    SyntaxListBase(SyntaxKind::TokenList, elements.size()), span<Token>(elements) {
}

template<typename T>
SeparatedSyntaxList<T>::SeparatedSyntaxList(span<TokenOrSyntax> elements) :
    SyntaxListBase(SyntaxKind::SeparatedList, elements.size()), elements(elements) {
}

} // namespace slang
