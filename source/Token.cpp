#include <cstdint>
#include <string>
#include <algorithm>

#include "BumpAllocator.h"
#include "StringRef.h"
#include "Token.h"
#include "StringTable.h"

namespace slang {

Token::Token(TokenKind kind, SourceLocation location, ArrayRef<Trivia> trivia, uint8_t flags) :
    location(location),
    kind(kind),
    trivia(trivia),
    flags(flags)
{
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

StringRef Token::rawText() const {
    StringRef text = getTokenKindText(kind);
    if (text)
        return text;
    else {
        // not a simple token, so extract info from our data pointer
        switch (kind) {
            case TokenKind::Unknown:
            case TokenKind::Identifier:
            case TokenKind::SystemIdentifier:
                return ((IdentifierInfo*)(this + 1))->rawText;
            case TokenKind::IncludeFileName:
            case TokenKind::StringLiteral:
                return ((StringLiteralInfo*)(this + 1))->rawText;
            case TokenKind::IntegerLiteral:
            case TokenKind::IntegerBase:
            case TokenKind::UnbasedUnsizedLiteral:
            case TokenKind::RealLiteral:
            case TokenKind::TimeLiteral:
                return ((NumericLiteralInfo*)(this + 1))->rawText;
            case TokenKind::Directive:
            case TokenKind::MacroUsage:
                return ((DirectiveInfo*)(this + 1))->rawText;
            case TokenKind::EndOfDirective:
            case TokenKind::EndOfFile:
                break;
            default:
                ASSERT(false && "What is this?");
        }
    }
    return nullptr;
}

void Token::writeTo(Buffer<char>& buffer, uint8_t writeFlags) const {
    if (!(writeFlags & SyntaxToStringFlags::IncludePreprocessed) && isFromPreprocessor())
        return;

    if (writeFlags & SyntaxToStringFlags::IncludeTrivia) {
        for (const auto& t : trivia)
            t.writeTo(buffer, writeFlags);
    }

    if (!(writeFlags & SyntaxToStringFlags::IncludeMissing) && isMissing())
        return;

    buffer.appendRange(rawText());
}

std::string Token::toString(uint8_t writeFlags) const {
    Buffer<char> buffer;
    writeTo(buffer, writeFlags);
    return std::string(buffer.begin(), buffer.end());
}

const NumericValue& Token::numericValue() const {
    ASSERT(kind == TokenKind::IntegerLiteral || kind == TokenKind::UnbasedUnsizedLiteral ||
           kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);

    return ((NumericLiteralInfo*)(this + 1))->value;
}

uint8_t Token::numericBaseFlags() const {
    ASSERT(kind == TokenKind::IntegerBase);

    return ((NumericLiteralInfo*)(this + 1))->baseFlags;
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

void Token::setNumericValue(const NumericValue& value) {
    ASSERT(kind == TokenKind::IntegerLiteral || kind == TokenKind::UnbasedUnsizedLiteral ||
           kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);
}

bool Token::hasTrivia(TriviaKind triviaKind) const {
    for (const auto& t : trivia) {
        if (t.kind == triviaKind)
            return true;
    }
    return false;
}

size_t Token::getAllocSize(TokenKind kind) {
    switch (kind) {
        case TokenKind::Unknown:
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
            return sizeof(Token) + sizeof(IdentifierInfo);
        case TokenKind::IntegerLiteral:
        case TokenKind::IntegerBase:
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
            return sizeof(Token) + sizeof(NumericLiteralInfo);
        case TokenKind::StringLiteral:
        case TokenKind::IncludeFileName:
            return sizeof(Token) + sizeof(StringLiteralInfo);
        case TokenKind::Directive:
            return sizeof(Token) + sizeof(DirectiveInfo);
        default:
            return sizeof(Token);
    }
}

Token* Token::create(BumpAllocator& alloc, TokenKind kind, SourceLocation location, ArrayRef<Trivia> trivia, uint8_t flags) {
    Token* token = (Token*)alloc.allocate((uint32_t)getAllocSize(kind));
    return new (token) Token(kind, location, trivia, flags);
}

Token* Token::createUnknown(BumpAllocator& alloc, SourceLocation location, ArrayRef<Trivia> trivia, StringRef rawText, uint8_t flags) {
    auto token = create(alloc, TokenKind::Unknown, location, trivia, flags);

    IdentifierInfo* info = (IdentifierInfo*)(token + 1);
    info->rawText = rawText;
    info->type = IdentifierType::Unknown;

    return token;
}

Token* Token::createSimple(BumpAllocator& alloc, TokenKind kind, SourceLocation location, ArrayRef<Trivia> trivia, uint8_t flags) {
    return create(alloc, kind, location, trivia, flags);
}

Token* Token::createIdentifier(BumpAllocator& alloc, TokenKind kind, SourceLocation location, ArrayRef<Trivia> trivia, StringRef rawText, IdentifierType type, uint8_t flags) {
    auto token = create(alloc, kind, location, trivia, flags);

    IdentifierInfo* info = (IdentifierInfo*)(token + 1);
    info->rawText = rawText;
    info->type = type;

    return token;
}

Token* Token::createStringLiteral(BumpAllocator& alloc, TokenKind kind, SourceLocation location, ArrayRef<Trivia> trivia, StringRef rawText, StringRef niceText, uint8_t flags) {
    auto token = create(alloc, kind, location, trivia, flags);

    StringLiteralInfo* info = (StringLiteralInfo*)(token + 1);
    info->rawText = rawText;
    info->niceText = niceText;

    return token;
}

Token* Token::createNumericLiteral(BumpAllocator& alloc, TokenKind kind, SourceLocation location, ArrayRef<Trivia> trivia, StringRef rawText, uint8_t baseFlags, uint8_t flags) {
    auto token = create(alloc, kind, location, trivia, flags);

    NumericLiteralInfo* info = (NumericLiteralInfo*)(token + 1);
    info->rawText = rawText;
    info->value = 0.0;
    info->baseFlags = baseFlags;

    return token;
}

Token* Token::createDirective(BumpAllocator& alloc, TokenKind kind, SourceLocation location, ArrayRef<Trivia> trivia, StringRef rawText, SyntaxKind directiveKind, uint8_t flags) {
    auto token = create(alloc, kind, location, trivia, flags);

    DirectiveInfo* info = (DirectiveInfo*)(token + 1);
    info->rawText = rawText;
    info->kind = directiveKind;

    return token;
}

Token* Token::missing(BumpAllocator& alloc, TokenKind kind, SourceLocation location, ArrayRef<Trivia> trivia) {
    switch (kind) {
        case TokenKind::Unknown:
            return createUnknown(alloc, location, trivia, nullptr, TokenFlags::Missing);
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
            return createIdentifier(alloc, kind, location, trivia, nullptr, IdentifierType::Unknown, TokenFlags::Missing);
        case TokenKind::IntegerLiteral:
        case TokenKind::IntegerBase:
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
            return createNumericLiteral(alloc, kind, location, trivia, nullptr, 0, TokenFlags::Missing);
        case TokenKind::StringLiteral:
        case TokenKind::IncludeFileName:
            return createStringLiteral(alloc, kind, location, trivia, nullptr, nullptr, TokenFlags::Missing);
        case TokenKind::Directive:
            return createDirective(alloc, kind, location, trivia, nullptr, SyntaxKind::Unknown, TokenFlags::Missing);
        default:
            return createSimple(alloc, kind, location, trivia, TokenFlags::Missing);
    }
}

Token* Token::clone(BumpAllocator& alloc) const {
    size_t size = getAllocSize(kind);
    auto cloned = (Token*)alloc.allocate((uint32_t)size);
    memcpy(cloned, this, size);

    return cloned;
}

}