#pragma once

namespace slang {

StringRef getTokenKindText(TokenKind kind);
TriviaKind getDirectiveKind(StringRef directive);

}