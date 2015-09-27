#pragma once

namespace slang {

enum class SyntaxKind : uint16_t;

class SyntaxNode {
public:
    SyntaxKind kind;

    SyntaxNode(SyntaxKind kind) : kind(kind) {}

    template<typename T>
    T* as() {
        // TODO: assert kind
        return static_cast<T*>(this);
    }
};

enum class SyntaxKind : uint16_t {
    Unknown,

    // directives
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
    UndefineAllDirective,

    // macros
    MacroUsage,
    MacroFormalArgumentList,
    MacroFormalArgument,
    MacroArgumentDefault
};

}