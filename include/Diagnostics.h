//------------------------------------------------------------------------------
// Diagnostics.h
// Diagnostic tracking and reporting.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <deque>
#include <string>
#include <unordered_map>
#include <variant>
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
    DecimalLiteralOverflow,
    VectorLiteralOverflow,

    // preprocessor
    CouldNotOpenIncludeFile,
    ExceededMaxIncludeDepth,
    UnknownDirective,
    ExpectedEndOfDirective,
    ExpectedEndOfMacroArgs,
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
    ExpectedIfOrCase,
    NoLabelOnSemicolon,
    DeferredDelayMustBeZero,
    AttributesNotSupported,

    // declarations
    DuplicateModule,
    NotePreviousDefinition,
    UnknownModule,
    DuplicateParameter,
    LocalParamNoInitializer,
    BodyParamNoInitializer,
    PackedDimRequiresConstantRange,
    PackedDimsOnPredefinedType,

    // expressions
    BadUnaryExpression,
    BadBinaryExpression,

    MaxValue
};

class Diagnostic;

/// The severity of a given diagnostic. This is not tied to the diagnostic itself;
/// it can be configured on a per-diagnostic basis at runtime.
enum class DiagnosticSeverity {
    Note,
    Warning,
    Error
};

/// Wraps up a reported diagnostic along with location in source and any arguments.
class Diagnostic {
public:
    // Diagnostic-specific arguments that can be used to better report messages.
    using Arg = std::variant<std::string, SourceRange, int>;
    std::vector<Arg> args;
    std::vector<SourceRange> ranges;

    /// The specific kind of diagnostic that was issued.
    DiagCode code;

    /// The location in source of the cause of the diagnostic.
    SourceLocation location;

    /// Constructs a new Diagnostic entry with the given code and location.
    Diagnostic(DiagCode code, SourceLocation location);

    /// Adds an argument to the diagnostic.
    friend Diagnostic& operator<<(Diagnostic& diag, Arg&& arg);
    friend Diagnostic& operator<<(Diagnostic& diag, StringRef arg);
};

std::ostream& operator<<(std::ostream& os, const Diagnostic::Arg& arg);

/// A collection of diagnostics.
class Diagnostics : public Buffer<Diagnostic> {
public:
    Diagnostics();

    /// Adds a new diagnostic to the collection.
    Diagnostic& add(DiagCode code, SourceLocation location);
};

class DiagnosticWriter {
public:
    DiagnosticWriter(SourceManager& sourceManager);

    /// Sets the message to use for the given diagnostic.
    void setMessage(DiagCode code, std::string format);

    /// Sets the severity to use for the given diagnostic.
    void setSeverity(DiagCode code, DiagnosticSeverity severity);

    /// Gets the current severity of the given diagnostic.
    DiagnosticSeverity getSeverity(DiagCode code) const;

    /// Writes a report for the given diagnostic.
    std::string report(const Diagnostic& diagnostic);

    /// Writes a report for all of the diagnostics in the given collection.
    /// Note that this modifies the collection by sorting it.
    std::string report(Diagnostics& diagnostics);

private:
    SourceLocation getFullyExpandedLoc(SourceLocation loc);
    StringRef getBufferLine(SourceLocation location, uint32_t col);
    bool sortDiagnostics(const Diagnostic& x, const Diagnostic& y);
    void getIncludeStack(BufferID buffer, std::deque<SourceLocation>& stack);
    void highlightRange(SourceRange range, SourceLocation caretLoc, uint32_t col, StringRef sourceLine, std::string& buffer);
    
    template<typename T>
    void formatDiag(T& writer, SourceLocation loc, const std::vector<SourceRange>& ranges,
                    const char* severity, const std::string& msg);

    SourceManager& sourceManager;

    // Little structure to hold a diagnostic's format and severity.
    struct Descriptor {
        std::string format;
        DiagnosticSeverity severity;
    };

    std::unordered_map<DiagCode, Descriptor> descriptors;
};

}