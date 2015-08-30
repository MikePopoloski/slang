#include "slang.h"

namespace slang {

void Token::writeTo(Buffer<char>& buffer, bool includeTrivia) const {
    if (includeTrivia) {
        for (const auto& t : trivia)
            buffer.appendRange(t.rawText);
    }

    StringRef text = GetTokenKindText(kind);
    if (text) {
        buffer.appendRange(text);
        return;
    }

    // not a simple token, so extract info from our data pointer
    switch (kind) {
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
            buffer.appendRange(identifier->rawText);
            break;
        case TokenKind::StringLiteral:
            buffer.appendRange(string->rawText);
            break;
        case TokenKind::IntegerLiteral:
        case TokenKind::RealLiteral:
            buffer.appendRange(numeric->rawText);
            break;
    }
}

StringRef Token::valueText() const {
    StringRef text = GetTokenKindText(kind);
    if (text)
        return text;

    switch (kind) {
        case TokenKind::Identifier:
            if (identifier->type == IdentifierType::Escaped)
                return identifier->rawText.subString(1); // strip off leading backslash
            else
                return identifier->rawText;
        case TokenKind::SystemIdentifier:
            return identifier->rawText;
        case TokenKind::StringLiteral:
            return string->niceText;
        default:
            return StringRef();
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
    return numeric->value;
}

IdentifierType Token::identifierType() const {
    ASSERT(kind == TokenKind::Identifier || kind == TokenKind::SystemIdentifier);
    return identifier->type;
}

}