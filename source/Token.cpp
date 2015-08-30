#include "slang.h"

namespace slang {

void Token::writeTo(Buffer<char>& buffer, bool includeTrivia) const {
    if (includeTrivia) {
        for (const auto& t : trivia)
            buffer.appendRange(t.rawText);
    }

    StringRef text = getTokenKindText(kind);
    if (text) {
        buffer.appendRange(text);
        return;
    }

    // not a simple token, so extract info from our data pointer
    switch (kind) {
        case TokenKind::Unknown:
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
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            buffer.appendRange(directive->rawText);
            break;
    }
}

StringRef Token::valueText() const {
    StringRef text = getTokenKindText(kind);
    if (text)
        return text;

    switch (kind) {
        case TokenKind::Identifier:
            switch (identifier->type) {
                case IdentifierType::Escaped:
                    // strip off leading backslash
                    return identifier->rawText.subString(1);
                case IdentifierType::Unknown:
                    // unknown tokens don't have value text
                    return nullptr;
                default:
                    return identifier->rawText;
            }
            break;
        case TokenKind::SystemIdentifier:
            return identifier->rawText;
        case TokenKind::StringLiteral:
            return string->niceText;
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            return directive->rawText;
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
    return numeric->value;
}

IdentifierType Token::identifierType() const {
    if (kind == TokenKind::Identifier || kind == TokenKind::SystemIdentifier)
        return identifier->type;
    return IdentifierType::Unknown;
}

TriviaKind Token::directiveKind() const {
    ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    return directive->kind;
}

}