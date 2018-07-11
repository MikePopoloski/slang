//------------------------------------------------------------------------------
// Diagnostics.h
// Diagnostic tracking and reporting.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <deque>
#include <string>
#include <unordered_map>
#include <vector>

#include "binding/ConstantValue.h"
#include "text/SourceLocation.h"
#include "util/SmallVector.h"

namespace slang {

class SourceManager;
class Type;

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
    IncludeNotFirstOnLine,
    TooManyLexerErrors,

    // numeric
    LiteralSizeIsZero,
    LiteralSizeTooLarge,
    RealExponentOverflow,
    SignedIntegerOverflow,
    DecimalLiteralOverflow,
    VectorLiteralOverflow,
    ValueMustNotBeUnknown,
    ValueMustBePositive,
    ValueExceedsMaxBitWidth,

    // preprocessor
    CouldNotOpenIncludeFile,
    ExceededMaxIncludeDepth,
    UnknownDirective,
    ExpectedEndOfDirective,
    UnexpectedConditionalDirective,
    UnbalancedMacroArgDims,
    ExpectedMacroArgs,
    ExpectedNetType,
    InvalidMacroName,
    TooManyActualMacroArgs,
    NotEnoughMacroArgs,
    InvalidLineDirectiveLevel,
    UndefineBuiltinDirective,
    UnrecognizedKeywordVersion,
    MismatchedEndKeywordsDirective,
    InvalidTimescaleSpecifier,
    IgnoredMacroPaste,
    SpuriousMacroToken,

    // parser
    ExpectedIdentifier,
    ExpectedToken,
    MisplacedTrailingSeparator,
    ImplicitNotAllowed,
    MultipleTypesInDeclaration,
    ColonShouldBeDot,
    ExpectedMember,
    ExpectedStatement,
    ExpectedParameterPort,
    ExpectedNonAnsiPort,
    ExpectedAnsiPort,
    ExpectedModportPort,
    ExpectedFunctionPort,
    ExpectedAssertionItemPort,
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
    ExpectedClassScope,
    NoLabelOnSemicolon,
    DeferredDelayMustBeZero,
    InvalidGenvarIterExpression,
    ExpectedGenvarIterVar,
    ConstFunctionPortRequiresRef,
    ExpectedClockingSkew,
    ExpectedDPISpecString,
    AttributesOnEmpty,
    AttributesOnClassParam,
    AttributesOnGenerateRegion,
    AttributesOnTimeDecl,

    // declarations
    DuplicateDefinition,
    NotePreviousDefinition,
    UnknownModule,
    LocalParamNoInitializer,
    BodyParamNoInitializer,
    UnpackedDimensionRequired,
    UnpackedDimensionRequiresConstRange,
    PackedDimRequiresConstantRange,
    PackedDimsOnPredefinedType,
    DimensionOutOfRange,
    MixingOrderedAndNamedParams,
    DuplicateParamAssignment,
    NotePreviousUsage,
    ParamHasNoValue,
    ModuleUnreferenced,
    NoteDeclarationHere,
    TooManyParamAssignments,
    AssignedToLocalPortParam,
    AssignedToLocalBodyParam,
    ParameterDoesNotExist,
    DuplicateAttribute,
    PackedMemberNotIntegral,
    PackedMemberHasInitializer,
    Redefinition,
    RedefinitionDifferentType,
    RedefinitionDifferentSymbolKind,
    UnresolvedForwardTypedef,
    ForwardTypedefDoesNotMatch,

    // expressions
    BadUnaryExpression,
    BadBinaryExpression,
    BadIndexExpression,
    BadConcatExpression,
    CannotIndexScalar,
    IndexMustBeIntegral,
    ArgMustBeIntegral,
    BadAssignment,
    NoImplicitConversion,
    TooManyArguments,
    ExpressionNotAssignable,
    ReplicationZeroOutsideConcat,
    MemberAccessNotStructUnion,
    ExpressionNotCallable,

    // statements
    ReturnNotInSubroutine,

    // types
    InvalidEnumBase,
    NetTypeNotAllowed,

    // lookups
    AmbiguousWildcardImport,
    NoteImportedFrom,
    ImportNameCollision,
    UndeclaredIdentifier,
    UnknownClassOrPackage,
    UsedBeforeDeclared,
    NotAType,
    NotAValue,
    NotASubroutine,
    NotAHierarchicalScope,
    HierarchicalNotAllowedInConstant,
    UnknownMember,
    RecursiveDefinition,

    // constant evaluation
    ExpressionNotConstant,
    NoteInCallTo,
    NoteNonConstVariable,
    NoteArrayIndexInvalid,
    NotePartSelectInvalid,
    NoteHierarchicalNameInCE,
    NoteFunctionIdentifiersMustBeLocal,
    NoteParamUsedInCEBeforeDecl,

    MaxValue
};

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
    using ArgVariantType = std::variant<std::string, int64_t, uint64_t, const Type*, ConstantValue>;
    struct Arg : public ArgVariantType {
        using ArgVariantType::variant;
        friend std::ostream& operator<<(std::ostream& os, const Arg& arg);
    };
    std::vector<Arg> args;
    std::vector<SourceRange> ranges;
    std::vector<Diagnostic> notes;

    /// The specific kind of diagnostic that was issued.
    DiagCode code;

    /// The location in source of the cause of the diagnostic.
    SourceLocation location;

    /// Constructs a new Diagnostic entry with the given code and location.
    Diagnostic(DiagCode code, SourceLocation location);

    /// Adds a new note to the diagnostic at the given source location.
    Diagnostic& addNote(DiagCode code, SourceLocation location);
    Diagnostic& addNote(const Diagnostic& diag);

    /// Adds an argument to the diagnostic.
    friend Diagnostic& operator<<(Diagnostic& diag, const Type& arg);
    friend Diagnostic& operator<<(Diagnostic& diag, string_view arg);
    friend Diagnostic& operator<<(Diagnostic& diag, SourceRange arg);
    friend Diagnostic& operator<<(Diagnostic& diag, const ConstantValue& arg);

    template<typename T, typename = std::enable_if_t<std::is_integral_v<T> && std::is_signed_v<T>>>
    inline friend Diagnostic& operator<<(Diagnostic& diag, T arg) {
        diag.args.emplace_back((int64_t)arg);
        return diag;
    }

    template<typename T, typename = void, typename = std::enable_if_t<std::is_integral_v<T> && std::is_unsigned_v<T>>>
    inline friend Diagnostic& operator<<(Diagnostic& diag, T arg) {
        diag.args.emplace_back((uint64_t)arg);
        return diag;
    }
};

/// A collection of diagnostics.
class Diagnostics : public SmallVectorSized<Diagnostic, 8> {
public:
    Diagnostics() = default;

    Diagnostics(Diagnostics&& other) noexcept :
        SmallVectorSized<Diagnostic, 8>(std::move(other)) {}
    Diagnostics& operator=(Diagnostics&& other) = default;

    /// Adds a new diagnostic to the collection, pointing to the given source location.
    Diagnostic& add(DiagCode code, SourceLocation location);

    /// Adds a new diagnostic to the collection, highlighting the given source range.
    Diagnostic& add(DiagCode code, SourceRange range);

    /// Sorts the diagnostics in the collection based on source file and line number.
    void sort(const SourceManager& sourceManager);
};

class DiagnosticWriter {
public:
    explicit DiagnosticWriter(const SourceManager& sourceManager);

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
    std::string report(const Diagnostics& diagnostics);

private:
    string_view getBufferLine(SourceLocation location, uint32_t col);
    void getIncludeStack(BufferID buffer, std::deque<SourceLocation>& stack);
    void highlightRange(SourceRange range, SourceLocation caretLoc, uint32_t col, string_view sourceLine, std::string& buffer);

    template<typename T>
    void formatDiag(T& buffer, SourceLocation loc, const std::vector<SourceRange>& ranges,
                    const char* severity, const std::string& msg);

    const SourceManager& sourceManager;

    // Little structure to hold a diagnostic's format and severity.
    struct Descriptor {
        std::string format;
        DiagnosticSeverity severity;
    };

    std::unordered_map<DiagCode, Descriptor> descriptors;
};

}
