#pragma once

namespace slang {

enum class DiagCode : uint8_t {
    UnterminatedBlockComment,
    NonPrintableChar,
    MisplacedDirectiveChar,
    EscapedWhitespace,
    NewlineInStringLiteral,
    UnterminatedStringLiteral,
    SplitBlockCommentInDirective,
    MissingExponentDigits
};

class SyntaxError {
public:
    DiagCode code;
    int location;
    int width;

    SyntaxError(DiagCode code, int location, int width)
        : code(code), location(location), width(width) {
    }
};

class Diagnostics {
public:
    Diagnostics();

    void add(const SyntaxError& error);

private:
    Buffer<SyntaxError> syntaxErrors;
};

}