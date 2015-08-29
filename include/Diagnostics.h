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

class Diagnostics {
};

}