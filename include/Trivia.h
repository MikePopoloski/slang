#pragma once

namespace slang {

enum class TriviaKind : uint8_t {
    Unknown,
    Whitespace,
    EndOfLine,
    LineContinuation,
    LineComment,
    BlockComment,
    DisabledText,
    SkippedTokens,
    MacroUsage,
    BeginKeywordsDirective,
    CellDefineDirective,
    DefaultNetTypeDirective,
    DefineDirective,
    ElseDirective,
    ElseIfDirective,
    EndKeywordsDirective,
    EndCellDefineDirective,
    EndIfDirective,
    IfDefDirective,
    IfNDefDirective,
    IncludeDirective,
    LineDirective,
    NoUnconnectedDriveDirective,
    PragmaDirective,
    ResetAllDirective,
    TimescaleDirective,
    UnconnectedDriveDirective,
    UndefDirective,
    UndefineAllDirective
};

std::ostream& operator<<(std::ostream& os, TriviaKind kind);

struct Trivia {
    StringRef rawText;
    TriviaKind kind;

    Trivia(TriviaKind kind, StringRef rawText) :
        rawText(rawText), kind(kind) {
    }
};

}