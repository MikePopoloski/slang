#pragma once

namespace slang {

enum class TriviaKind : uint8_t {
    Unknown,
    Whitespace,
    EndOfLine,
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

struct Trivia {
    StringRef rawText;
    TriviaKind kind;

    Trivia(TriviaKind kind, StringRef rawText)
        : rawText(rawText), kind(kind) {
    }

    void WriteTo(std::string& buffer) const;
};

}