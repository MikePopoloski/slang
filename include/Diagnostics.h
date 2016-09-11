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
    VectorDigitsLeadingUnderscore,
    DecimalDigitMultipleUnknown,
    BadBinaryDigit,
    BadOctalDigit,
    BadDecimalDigit,
    BadHexDigit,

    // numeric
    LiteralSizeIsZero,
    LiteralSizeTooLarge,
    RealExponentOverflow,
    SignedIntegerOverflow,
    IntegerVectorOverflow,
    DecimalLiteralOverflow,
    TooManyLiteralDigits,

    // preprocessor
    CouldNotOpenIncludeFile,
    ExceededMaxIncludeDepth,
    UnknownDirective,
    ExpectedEndOfDirective,
    ExpectedEndOfMacroArgs,
    ExpectedEndIfDirective,
    UnexpectedConditionalDirective,
    UnbalancedMacroArgDims,
    ExpectedMacroArgs,
    ExpectedNetType,
    InvalidMacroName,
    TooManyActualMacroArgs,
    NotEnoughMacroArgs,

    // parser
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
    ExpectedOpenRangeElement,
    ExpectedStreamExpression,
    ExpectedArgument,
    ExpectedVariableDeclarator,
    ExpectedConditionalPattern,
    ExpectedAttribute,
    ExpectedPackageImport,
    ExpectedHierarchicalInstantiation,
    ExpectedPortConnection,
    ExpectedVectorDigits,
    ExpectedVariableAssignment,
    ExpectedInterfaceClassName,
    ExpectedAssignmentKey,
    ExpectedDistItem,

    // declarations
    ModuleRedefinition,
    UnknownModule
};

class Diagnostic;

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

    DiagnosticReport toReport() const;

    friend Diagnostic& operator <<(Diagnostic& diag, Arg&& arg);
};

class Diagnostics : public Buffer<Diagnostic> {
public:
    Diagnostics();

    Diagnostic& add(DiagCode code, SourceLocation location);

    std::string reportAll(SourceManager& sourceManager);
};

}