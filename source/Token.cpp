#include "slang.h"

namespace slang {

void Token::WriteTo(std::string& buffer, bool includeTrivia) const {
    if (includeTrivia) {
        for (const auto& t : trivia)
            t.rawText.copyTo(buffer);
    }

    const char* text = GetTokenKindText(kind);
    if (text != nullptr) {
        buffer.append(text);
        return;
    }

    // not a simple token, so extract info from our data pointer
    switch (kind) {
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
            identifier->text.copyTo(buffer);
            break;
        case TokenKind::StringLiteral:
            string->rawText.copyTo(buffer);
            break;
    }
}

StringRef Token::GetValueText() const {
    switch (kind) {
        case TokenKind::StringLiteral:
            return string->niceText;
        default:
            return StringRef();
    }
}

std::string Token::ToString() const {
    std::string buffer;
    WriteTo(buffer, false);
    return buffer;
}

std::string Token::ToFullString() const {
    std::string buffer;
    WriteTo(buffer, true);
    return buffer;
}

}