#pragma once

namespace slang {

StringRef getTokenKindText(TokenKind kind);
StringRef getTriviaKindText(TriviaKind kind);
TriviaKind getDirectiveKind(StringRef directive);

}