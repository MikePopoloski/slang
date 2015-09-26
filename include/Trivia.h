#pragma once

namespace slang {

class Token;

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
    TriviaKind kind;

    Trivia(TriviaKind kind) : kind(kind) {}

    virtual void writeTo(Buffer<char>& buffer) = 0;
};

struct SimpleTrivia : public Trivia {
    StringRef rawText;

    SimpleTrivia(TriviaKind kind, StringRef rawText) :
        Trivia(kind), rawText(rawText) {
    }

    void writeTo(Buffer<char>& buffer) override;
};

struct SimpleDirectiveTrivia : public Trivia {
    Token* directive;
    Token* endOfDirective;

    SimpleDirectiveTrivia(TriviaKind kind, Token* directive, Token* endOfDirective) :
        Trivia(kind),
        directive(directive),
        endOfDirective(endOfDirective) {
    }

    void writeTo(Buffer<char>& buffer) override;
};

struct IncludeDirectiveTrivia : public Trivia {
    Token* directive;
    Token* fileName;
    Token* endOfDirective;

    IncludeDirectiveTrivia(Token* directive, Token* fileName, Token* endOfDirective) :
        Trivia(TriviaKind::IncludeDirective),
        directive(directive),
        fileName(fileName),
        endOfDirective(endOfDirective) {
    }

    void writeTo(Buffer<char>& buffer) override;
};

struct MacroArgumentDefault {
    Token* equals;
    ArrayRef<Token*> tokens;
};

struct MacroFormalArgument {
    Token* name;
    MacroArgumentDefault* defaultValue;

    MacroFormalArgument(Token* name, MacroArgumentDefault* def) :
        name(name), defaultValue(def) {
    }
};

struct MacroFormalArgumentList {
    Token* openParen;
    ArrayRef<MacroFormalArgument*> args;
    ArrayRef<Token*> commaSeparators;
    Token* closeParen;

    MacroFormalArgumentList(
        Token* openParen,
        ArrayRef<MacroFormalArgument*> args,
        ArrayRef<Token*> commaSeparators,
        Token* closeParen
    );
};

struct DefineDirectiveTrivia : public Trivia {
    Token* directive;
    Token* name;
    Token* endOfDirective;
    MacroFormalArgumentList* formalArguments;
    ArrayRef<Token*> body;

    DefineDirectiveTrivia(
        Token* directive,
        Token* name,
        Token* endOfDirective,
        MacroFormalArgumentList* formalArguments,
        ArrayRef<Token*> body
    );

    void writeTo(Buffer<char>& buffer) override;
};

struct SkippedTokensTrivia : public Trivia {
    ArrayRef<Token*> tokens;

    SkippedTokensTrivia(ArrayRef<Token*> tokens) :
        Trivia(TriviaKind::SkippedTokens), tokens(tokens) {
    }

    void writeTo(Buffer<char>& buffer) override;
};

}