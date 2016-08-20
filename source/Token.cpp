#include "Token.h"

#include "BumpAllocator.h"

namespace slang {

Token::Token() :
    kind(TokenKind::Unknown), info(nullptr)
{
}

Token::Token(TokenKind kind, const Info* info) :
    kind(kind), info(info)
{
    ASSERT(info);
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
                    return info->rawText.subString(1);
                case IdentifierType::Unknown:
                    // unknown tokens don't have value text
                    return nullptr;
                default:
                    return info->rawText;
            }
            break;
        case TokenKind::SystemIdentifier:
            return info->rawText;
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
            return info->stringText;
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            return info->rawText;
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
            case TokenKind::IncludeFileName:
            case TokenKind::StringLiteral:
            case TokenKind::IntegerLiteral:
            case TokenKind::IntegerBase:
            case TokenKind::UnbasedUnsizedLiteral:
            case TokenKind::RealLiteral:
            case TokenKind::TimeLiteral:
            case TokenKind::Directive:
            case TokenKind::MacroUsage:
                return info->rawText;
            case TokenKind::EndOfDirective:
            case TokenKind::EndOfFile:
                break;
            default:
                ASSERT(false, "Unknown token kind: %u", (uint32_t)kind);
        }
    }
    return nullptr;
}

void Token::writeTo(Buffer<char>& buffer, uint8_t writeFlags) const {
    if (!(writeFlags & SyntaxToStringFlags::IncludePreprocessed) && isFromPreprocessor())
        return;

    if (writeFlags & SyntaxToStringFlags::IncludeTrivia) {
        for (const auto& t : info->trivia)
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
    return info->numInfo.value;
}

uint8_t Token::numericFlags() const {
    ASSERT(kind == TokenKind::IntegerBase || kind == TokenKind::TimeLiteral);
    return info->numInfo.numericFlags;
}

IdentifierType Token::identifierType() const {
    if (kind == TokenKind::Identifier || kind == TokenKind::SystemIdentifier)
        return info->idType;
    return IdentifierType::Unknown;
}

SyntaxKind Token::directiveKind() const {
    ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    return info->directiveKind;
}

bool Token::hasTrivia(TriviaKind triviaKind) const {
    for (const auto& t : info->trivia) {
        if (t.kind == triviaKind)
            return true;
    }
    return false;
}

Token Token::asPreprocessed(BumpAllocator& alloc) const {
    auto newInfo = alloc.emplace<Info>(*info);
    newInfo->flags |= TokenFlags::IsFromPreprocessor;
    return Token(kind, newInfo);
}

Token Token::withTrivia(BumpAllocator& alloc, ArrayRef<Trivia> trivia) const {
    auto newInfo = alloc.emplace<Info>(*info);
    newInfo->trivia = trivia;
    return Token(kind, newInfo);
}

Token Token::withLocation(BumpAllocator& alloc, SourceLocation location) const {
    auto newInfo = alloc.emplace<Info>(*info);
    newInfo->location = location;
    return Token(kind, newInfo);
}

Token Token::createMissing(BumpAllocator& alloc, TokenKind kind, SourceLocation location) {
    auto info = alloc.emplace<Info>();
    info->location = location;
    info->flags = TokenFlags::Missing;

    return Token(kind, info);
}

}