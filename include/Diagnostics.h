#pragma once

#include <cstdint>
#include <deque>
#include <string>

#include "Buffer.h"
#include "SourceLocation.h"
#include "StringRef.h"

namespace slang {

class SourceManager;

enum class DiagCode : uint8_t {
    // lexer
    NonPrintableChar,
    UTF8Char,
    UnicodeBOM,
    EmbeddedNull,
    MisplacedDirectiveChar,
    EscapedWhitespace,
    ExpectedClosingQuote,
    UnterminatedBlockComment,
    NestedBlockComment,
    SplitBlockCommentInDirective,
    ExpectedIntegerBaseAfterSigned,
    MissingFractionalDigits,
    OctalEscapeCodeTooBig,
    InvalidHexEscapeCode,
    UnknownEscapeCode,
    ExpectedIncludeFileName,
    MissingExponentDigits,

    // preprocessor
    CouldNotOpenIncludeFile,
    ExceededMaxIncludeDepth,
    UnknownDirective,
    ExpectedEndOfDirective,
    ExpectedEndOfMacroArgs,
    ExpectedEndIfDirective,
    UnexpectedDirective,
    UnbalancedMacroArgDims,
    ExpectedMacroArgs,

    // parser
    SyntaxError,
    ExpectedIdentifier,
    ExpectedToken,
    ImplicitNotAllowed,
    MultipleTypesInDeclaration,
    DirectionOnInterfacePort,
    ColonShouldBeDot,
    InvalidTokenInMemberList,
    InvalidTokenInSequentialBlock,
    ExpectedStatement,
    ExpectedParameterPort,
    ExpectedNonAnsiPort,
    ExpectedAnsiPort,
    ExpectedForInitializer,
    ExpectedExpression,
    ExpectedInsideElement,
    ExpectedStreamExpression,
    ExpectedArgument,
    ExpectedVariableDeclarator,
    ExpectedConditionalPattern,
    ExpectedAttribute,
    ExpectedPackageImport,
    ExpectedHierarchicalInstantiation,
    ExpectedPortConnection,
    ExpectedVectorDigits,
    ExpectedVariableAssignment
};

class Diagnostic {
public:
    struct Arg {
        StringRef strRef;
        uint8_t type;

        Arg(StringRef strRef);

        friend std::ostream& operator <<(std::ostream& os, const Arg& arg);

        enum {
            STRINGREF
        };
    };

    std::deque<Arg> args;
    DiagCode code;
    SourceLocation location;

    Diagnostic(DiagCode code, SourceLocation location);

    friend Diagnostic& operator <<(Diagnostic& diag, Arg&& arg);
};

enum class DiagnosticSeverity {
    Info,
    Warning,
    Error
};

class DiagnosticReport {
public:
    const Diagnostic& diagnostic;
    StringRef format;
    DiagnosticSeverity severity;

    DiagnosticReport(const Diagnostic& diagnostic, StringRef format, DiagnosticSeverity severity);

    std::string toString(SourceManager& sourceManager) const;
};

class Diagnostics : public Buffer<Diagnostic> {
public:
    Diagnostics();

    Diagnostic& add(DiagCode code, SourceLocation location);
    DiagnosticReport getReport(const Diagnostic& diagnostic) const;
};

}