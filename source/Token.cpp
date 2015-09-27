#include <cstdint>
#include <string>
#include <algorithm>

#include "BumpAllocator.h"
#include "StringRef.h"
#include "Token.h"
#include "StringTable.h"

namespace slang {

Token::Token(TokenKind kind, ArrayRef<Trivia> trivia) :
    kind(kind), trivia(trivia) {
}

void Token::writeTo(Buffer<char>& buffer, bool includeTrivia) const {
    if (includeTrivia) {
        for (const auto& t : trivia)
            t.writeTo(buffer);
    }

    StringRef text = getTokenKindText(kind);
    if (text)
        buffer.appendRange(text);
    else {
        // not a simple token, so extract info from our data pointer
        switch (kind) {
            case TokenKind::Unknown:
            case TokenKind::Identifier:
            case TokenKind::SystemIdentifier:
                buffer.appendRange(((IdentifierInfo*)(this + 1))->rawText);
                break;
            case TokenKind::IncludeFileName:
            case TokenKind::StringLiteral:
                buffer.appendRange(((StringLiteralInfo*)(this + 1))->rawText);
                break;
            case TokenKind::IntegerLiteral:
            case TokenKind::RealLiteral:
                buffer.appendRange(((NumericLiteralInfo*)(this + 1))->rawText);
                break;
            case TokenKind::Directive:
            case TokenKind::MacroUsage:
                buffer.appendRange(((DirectiveInfo*)(this + 1))->rawText);
                break;
        }
    }
}

StringRef Token::valueText() const {
    StringRef text = getTokenKindText(kind);
    if (text)
        return text;

    switch (kind) {
        case TokenKind::Identifier:
            switch (identifierType()) {
                case IdentifierType::Escaped:
                    // strip off leading backslash
                    return ((IdentifierInfo*)(this + 1))->rawText.subString(1);
                case IdentifierType::Unknown:
                    // unknown tokens don't have value text
                    return nullptr;
                default:
                    return ((IdentifierInfo*)(this + 1))->rawText;
            }
            break;
        case TokenKind::SystemIdentifier:
            return ((IdentifierInfo*)(this + 1))->rawText;
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
            return ((StringLiteralInfo*)(this + 1))->niceText;
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            return ((DirectiveInfo*)(this + 1))->rawText;
        default:
            return nullptr;
    }
}

std::string Token::toString() const {
    Buffer<char> buffer;
    writeTo(buffer, false);
    return std::string(buffer.begin(), buffer.end());
}

std::string Token::toFullString() const {
    Buffer<char> buffer;
    writeTo(buffer, true);
    return std::string(buffer.begin(), buffer.end());
}

const NumericValue& Token::numericValue() const {
    ASSERT(kind == TokenKind::IntegerLiteral || kind == TokenKind::RealLiteral);
    return ((NumericLiteralInfo*)(this + 1))->value;
}

IdentifierType Token::identifierType() const {
    if (kind == TokenKind::Identifier || kind == TokenKind::SystemIdentifier)
        return ((IdentifierInfo*)(this + 1))->type;
    return IdentifierType::Unknown;
}

SyntaxKind Token::directiveKind() const {
    ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    return ((DirectiveInfo*)(this + 1))->kind;
}

Token* Token::createUnknown(BumpAllocator& alloc, ArrayRef<Trivia> trivia, StringRef rawText) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(IdentifierInfo));
    new (token) Token(TokenKind::Unknown, trivia);

    IdentifierInfo* info = (IdentifierInfo*)(token + 1);
    info->rawText = rawText;
    info->type = IdentifierType::Unknown;

    return token;
}

Token* Token::createSimple(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia> trivia) {
    Token* token = (Token*)alloc.allocate(sizeof(Token));
    new (token) Token(kind, trivia);
    return token;
}

Token* Token::createIdentifier(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia> trivia, StringRef rawText, IdentifierType type) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(IdentifierInfo));
    new (token) Token(kind, trivia);

    IdentifierInfo* info = (IdentifierInfo*)(token + 1);
    info->rawText = rawText;
    info->type = type;

    return token;
}

Token* Token::createStringLiteral(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia> trivia, StringRef rawText, StringRef niceText) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(StringLiteralInfo));
    new (token) Token(kind, trivia);

    StringLiteralInfo* info = (StringLiteralInfo*)(token + 1);
    info->rawText = rawText;
    info->niceText = niceText;

    return token;
}

Token* Token::createNumericLiteral(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia> trivia, StringRef rawText, NumericValue value) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(NumericLiteralInfo));
    new (token) Token(kind, trivia);

    NumericLiteralInfo* info = (NumericLiteralInfo*)(token + 1);
    info->rawText = rawText;
    info->value = value;

    return token;
}

Token* Token::createDirective(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia> trivia, StringRef rawText, SyntaxKind directiveKind) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(DirectiveInfo));
    new (token) Token(kind, trivia);

    DirectiveInfo* info = (DirectiveInfo*)(token + 1);
    info->rawText = rawText;
    info->kind = directiveKind;

    return token;
}

Token* Token::missing(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia> trivia) {
    // TODO: flag missing
    switch (kind) {
        case TokenKind::Unknown:
            return createUnknown(alloc, trivia, nullptr);
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
            return createIdentifier(alloc, kind, trivia, nullptr, IdentifierType::Unknown);
        case TokenKind::IntegerLiteral:
        case TokenKind::RealLiteral:
            return createNumericLiteral(alloc, kind, trivia, nullptr, 0);
        case TokenKind::StringLiteral:
        case TokenKind::IncludeFileName:
            return createStringLiteral(alloc, kind, trivia, nullptr, nullptr);
        case TokenKind::Directive:
            return createDirective(alloc, kind, trivia, nullptr, SyntaxKind::Unknown);
        default:
            return createSimple(alloc, kind, trivia);
    }
}

}