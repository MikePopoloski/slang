//------------------------------------------------------------------------------
// Diagnostics.h
// Diagnostic tracking and reporting.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <string>
#include <vector>

#include "Buffer.h"
#include "SourceLocation.h"
#include "StringRef.h"

namespace slang {

class SourceManager;

/// Complete set of diagnostic codes.
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

/// The severity of a given diagnostic. This is not tied to the diagnostic itself;
/// it can be configured on a per-diagnostic basis at runtime.
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

/// Wraps up a reported diagnostic along with location in source and any arguments.
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

    // Diagnostic-specific arguments that can be used to better report messages.
    std::vector<Arg> args;

    /// The specific kind of diagnostic that was issued.
    DiagCode code;

    /// The location in source of the cause of the diagnostic.
    SourceLocation location;

    Diagnostic(DiagCode code, SourceLocation location);

    DiagnosticReport toReport() const;

    /// Adds an argument to the diagnostic.
    friend Diagnostic& operator<<(Diagnostic& diag, Arg&& arg);
};

/// A collection of diagnostics along with reporting functionality.
class Diagnostics : public Buffer<Diagnostic> {
public:
    Diagnostics();

    /// Adds a new diagnostic to the collection.
    Diagnostic& add(DiagCode code, SourceLocation location);

    /// Generates a report string. Takes a SourceManager to resolve source information
    /// such as line numbers and file names.
    std::string reportAll(SourceManager& sourceManager);
};

}