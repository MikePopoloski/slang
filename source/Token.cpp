#include "slang.h"

namespace slang {

void Trivia::WriteTo(std::string& buffer) const {
    rawText.CopyTo(buffer);
}

void Token::WriteTo(std::string& buffer, bool includeTrivia) const {
    if (includeTrivia) {
        for (const auto& t : trivia)
            t.WriteTo(buffer);
    }

    const char* text = GetTokenKindText(kind);
    if (text != nullptr) {
        buffer.append(text);
        return;
    }

    // not a simple token, so extract info from our data pointer
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