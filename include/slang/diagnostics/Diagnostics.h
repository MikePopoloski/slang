//------------------------------------------------------------------------------
// Diagnostics.h
// Diagnostic definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <string>
#include <vector>

#include "slang/binding/ConstantValue.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/SmallVector.h"

namespace slang {

class SourceManager;
class Symbol;
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
    ValueMustBeIntegral,
    ValueMustNotBeUnknown,
    ValueMustBePositive,
    ValueExceedsMaxBitWidth,
    ValueOutOfRange,

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
    RecursiveMacro,
    MacroOpsOutsideDefinition,

    // parser
    ExpectedIdentifier,
    ExpectedStringLiteral,
    ExpectedIntegerLiteral,
    ExpectedTimeLiteral,
    ExpectedToken,
    MisplacedTrailingSeparator,
    ImplicitNotAllowed,
    MultipleTypesInDeclaration,
    InvalidAccessDotColon,
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
    NotePreviousDefinition,
    LocalParamNoInitializer,
    BodyParamNoInitializer,
    InvalidDimensionRange,
    DimensionRequiresConstRange,
    PackedDimsRequireFullRange,
    PackedDimsOnPredefinedType,
    MixingOrderedAndNamedParams,
    DuplicateParamAssignment,
    NotePreviousUsage,
    ParamHasNoValue,
    NoteDeclarationHere,
    TooManyParamAssignments,
    AssignedToLocalPortParam,
    AssignedToLocalBodyParam,
    ParameterDoesNotExist,
    DuplicateAttribute, // TODO:
    PackedMemberNotIntegral,
    PackedMemberHasInitializer,
    Redefinition,
    RedefinitionDifferentType,
    RedefinitionDifferentSymbolKind,
    UnresolvedForwardTypedef,
    ForwardTypedefDoesNotMatch,
    PortTypeNotInterfaceOrData,
    VarWithInterfacePort,
    DirectionWithInterfacePort,
    InOutPortCannotBeVariable,
    RefPortMustBeVariable,
    MissingPortIODeclaration,
    CantDeclarePortSigned,
    PortDeclDimensionsMismatch,
    UnknownPackage,
    MixingOrderedAndNamedPorts,
    DuplicateWildcardPortConnection,
    DuplicatePortConnection,
    TooManyPortConnections,
    UnconnectedNamedPort,
    PortDoesNotExist,
    InterfacePortNotConnected,
    InterfacePortInvalidExpression,

    // expressions
    BadUnaryExpression,
    BadBinaryExpression,
    BadIndexExpression,
    BadConcatExpression,
    CannotIndexScalar,
    IndexMustBeIntegral,
    BadAssignment,
    NoImplicitConversion,
    TooManyArguments,
    ExpressionNotAssignable,
    ReplicationZeroOutsideConcat,
    InvalidMemberAccess,
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
    NotAHierarchicalScope,
    NotAModport,
    NotAnInterface,
    HierarchicalNotAllowedInConstant,
    UnknownMember,
    UnknownPackageMember,
    RecursiveDefinition,
    ImplicitNamedPortNotFound,
    ImplicitNamedPortTypeMismatch,
    UnexpectedSystemName,
    UnknownSystemMethod,
    ScopeNotIndexable,
    InvalidScopeIndexExpression,
    ScopeIndexOutOfRange,
    CouldNotResolveHierarchicalPath,

    // constant evaluation
    ExpressionNotConstant,
    NoteInCallTo,
    NoteNonConstVariable,
    NoteArrayIndexInvalid,
    NotePartSelectInvalid, // TODO:
    NoteHierarchicalNameInCE,
    NoteFunctionIdentifiersMustBeLocal,
    NoteParamUsedInCEBeforeDecl,

    NotYetSupported,
    MaxValue
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

    /// The symbol in which the diagnostic occurred, or null if not applicable.
    const Symbol* symbol = nullptr;

    /// Constructs a new Diagnostic entry with the given code and location.
    Diagnostic(DiagCode code, SourceLocation location);

    /// Constructs a new Diagnostic entry with the given symbol, code and location.
    Diagnostic(const Symbol& source, DiagCode code, SourceLocation location);

    /// Adds a new note to the diagnostic at the given source location.
    Diagnostic& addNote(DiagCode code, SourceLocation location);
    Diagnostic& addNote(const Diagnostic& diag);

    /// Returns true if this diagnostic should be suppressed. This can happen, e.g. because it was
    /// issued inside of a generate block that was not instantiated.
    bool isSuppressed() const;

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

    template<typename T, typename = void,
             typename = std::enable_if_t<std::is_integral_v<T> && std::is_unsigned_v<T>>>
    inline friend Diagnostic& operator<<(Diagnostic& diag, T arg) {
        diag.args.emplace_back((uint64_t)arg);
        return diag;
    }
};

/// A collection of diagnostics.
class Diagnostics : public SmallVectorSized<Diagnostic, 8> {
public:
    Diagnostics() = default;

    Diagnostics(Diagnostics&& other) noexcept : SmallVectorSized<Diagnostic, 8>(std::move(other)) {}
    Diagnostics& operator=(Diagnostics&& other) = default;

    /// Adds a new diagnostic to the collection, pointing to the given source location.
    Diagnostic& add(DiagCode code, SourceLocation location);

    /// Adds a new diagnostic to the collection, highlighting the given source range.
    Diagnostic& add(DiagCode code, SourceRange range);

    /// Adds a new diagnostic to the collection, pointing to the given source location.
    Diagnostic& add(const Symbol& source, DiagCode code, SourceLocation location);

    /// Adds a new diagnostic to the collection, highlighting the given source range.
    Diagnostic& add(const Symbol& source, DiagCode code, SourceRange range);

    /// Sorts the diagnostics in the collection based on source file and line number.
    void sort(const SourceManager& sourceManager);
};

} // namespace slang
