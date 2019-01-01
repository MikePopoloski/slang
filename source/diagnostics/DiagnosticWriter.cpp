//------------------------------------------------------------------------------
// DiagnosticWriter.h
// Diagnostic rendering.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/DiagnosticWriter.h"

#include <fmt/ostream.h>

#include "slang/text/FormatBuffer.h"
#include "slang/text/SourceManager.h"
#include "slang/util/StackContainer.h"

namespace slang {

static const char* severityToString[] = { "note", "warning", "error" };

DiagnosticWriter::DiagnosticWriter(const SourceManager& sourceManager) :
    sourceManager(sourceManager) {
    // clang-format off
    // lexer
    descriptors[DiagCode::NonPrintableChar] = { "non-printable character in source text; SystemVerilog only supports ASCII text", DiagnosticSeverity::Error };
    descriptors[DiagCode::UTF8Char] = { "UTF-8 sequence in source text; SystemVerilog only supports ASCII text", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnicodeBOM] = { "Unicode BOM at start of source text; SystemVerilog only supports ASCII text", DiagnosticSeverity::Error };
    descriptors[DiagCode::EmbeddedNull] = { "embedded NUL in source text; are you sure this is source code?", DiagnosticSeverity::Error };
    descriptors[DiagCode::MisplacedDirectiveChar] = { "expected directive name", DiagnosticSeverity::Error };
    descriptors[DiagCode::EscapedWhitespace] = { "unexpected whitespace after escape character", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedClosingQuote] = { "missing closing quote", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnterminatedBlockComment] = { "block comment unclosed at end of file", DiagnosticSeverity::Error };
    descriptors[DiagCode::NestedBlockComment] = { "nested block comments are disallowed by SystemVerilog", DiagnosticSeverity::Error };
    descriptors[DiagCode::SplitBlockCommentInDirective] = { "block comments on the same line as a directive must also be terminated on that line", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedIntegerBaseAfterSigned] = { "expected integer base specifier after signed specifier", DiagnosticSeverity::Error };
    descriptors[DiagCode::MissingFractionalDigits] = { "expected fractional digits after decimal", DiagnosticSeverity::Error };
    descriptors[DiagCode::OctalEscapeCodeTooBig] = { "octal escape code is too large to be an ASCII character", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidHexEscapeCode] = { "invalid hexadecimal number", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnknownEscapeCode] = { "unknown character escape sequence", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedIncludeFileName] = { "expected an include file name", DiagnosticSeverity::Error };
    descriptors[DiagCode::MissingExponentDigits] = { "expected exponent digits", DiagnosticSeverity::Error };
    descriptors[DiagCode::VectorDigitsLeadingUnderscore] = { "vector literals must not start with a leading underscore", DiagnosticSeverity::Error };
    descriptors[DiagCode::DecimalDigitMultipleUnknown] = { "decimal literals cannot have multiple X or Z digits", DiagnosticSeverity::Error };
    descriptors[DiagCode::BadBinaryDigit] = { "expected binary digit", DiagnosticSeverity::Error };
    descriptors[DiagCode::BadOctalDigit] = { "expected octal digit", DiagnosticSeverity::Error };
    descriptors[DiagCode::BadDecimalDigit] = { "expected decimal digit", DiagnosticSeverity::Error };
    descriptors[DiagCode::BadHexDigit] = { "expected hexadecimal digit", DiagnosticSeverity::Error };
    descriptors[DiagCode::IncludeNotFirstOnLine] = { "include directives must begin on their own line", DiagnosticSeverity::Error };
    descriptors[DiagCode::TooManyLexerErrors] = { "lexer has encountered too many errors (input is a binary file?)", DiagnosticSeverity::Error };

    // numeric
    descriptors[DiagCode::LiteralSizeIsZero] = { "size of vector literal cannot be zero", DiagnosticSeverity::Error };
    descriptors[DiagCode::LiteralSizeTooLarge] = { "size of vector literal is too large (> {} bits)", DiagnosticSeverity::Error };
    descriptors[DiagCode::RealExponentOverflow] = { "real literal overflows 64 bits", DiagnosticSeverity::Error };
    descriptors[DiagCode::SignedIntegerOverflow] = { "signed integer overflows 32 bits", DiagnosticSeverity::Error };
    descriptors[DiagCode::DecimalLiteralOverflow] = { "decimal literal overflows 32 bits", DiagnosticSeverity::Error };
    descriptors[DiagCode::VectorLiteralOverflow] = { "vector literal too large for the given number of bits", DiagnosticSeverity::Warning };
    descriptors[DiagCode::ValueMustBeIntegral] = { "value must be integral", DiagnosticSeverity::Error };
    descriptors[DiagCode::ValueMustNotBeUnknown] = { "value must not have any unknown bits", DiagnosticSeverity::Error };
    descriptors[DiagCode::ValueMustBePositive] = { "value must be positive", DiagnosticSeverity::Error };
    descriptors[DiagCode::ValueExceedsMaxBitWidth] = { "value exceeds maximum vector width ({} bits)", DiagnosticSeverity::Error };
    descriptors[DiagCode::ValueOutOfRange] = { "{} is out of allowed range ({} to {})", DiagnosticSeverity::Error };

    // preprocessor
    descriptors[DiagCode::CouldNotOpenIncludeFile] = { "could not find or open include file", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExceededMaxIncludeDepth] = { "exceeded max include depth", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnknownDirective] = { "unknown macro or compiler directive '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedEndOfDirective] = { "expected end of directive (missing newline?)", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnexpectedConditionalDirective] = { "unexpected conditional directive", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnbalancedMacroArgDims] = { "unbalanced macro argument delimiters ((), [], or {{}}); didn't see an end '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedMacroArgs] = { "expected macro arguments for function-like macro", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedNetType] = { "expected net type specifier", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidMacroName] = { "can't redefine compiler directive as a macro", DiagnosticSeverity::Error };
    descriptors[DiagCode::TooManyActualMacroArgs] = { "too many arguments provided to function-like macro", DiagnosticSeverity::Error };
    descriptors[DiagCode::NotEnoughMacroArgs] = { "not enough arguments provided to function-like macro", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidLineDirectiveLevel] = { "invalid level for `line directive, must be 0, 1, or 2", DiagnosticSeverity::Error };
    descriptors[DiagCode::UndefineBuiltinDirective] = { "cannot `undef compiler directives", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnrecognizedKeywordVersion] = { "unsupported keyword version specified for `begin_keywords", DiagnosticSeverity::Error };
    descriptors[DiagCode::MismatchedEndKeywordsDirective] = { "no opening `begin_keywords directive", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidTimescaleSpecifier] = { "timescale specifiers must be powers of ten with precision more precise than unit", DiagnosticSeverity::Error };
    descriptors[DiagCode::IgnoredMacroPaste] = { "paste token is pointless because it is adjacent to whitespace", DiagnosticSeverity::Warning };
    descriptors[DiagCode::RecursiveMacro] = { "expansion of macro '{}' is recursive", DiagnosticSeverity::Error };
    descriptors[DiagCode::MacroOpsOutsideDefinition] = { "macro operators may only be used within a macro definition", DiagnosticSeverity::Error };

    // parser
    descriptors[DiagCode::ExpectedIdentifier] = { "expected identifier", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedStringLiteral] = { "expected string literal", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedIntegerLiteral] = { "expected integer literal", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedTimeLiteral] = { "expected time literal", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedToken] = { "expected '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::MisplacedTrailingSeparator] = { "misplaced trailing '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::ImplicitNotAllowed] = { "expected data type (implicit type name not allowed)", DiagnosticSeverity::Error };
    descriptors[DiagCode::MultipleTypesInDeclaration] = { "multiple types given in single declaration; this is not allowed in SystemVerilog", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidAccessDotColon] = { "invalid access token; '{}' should be '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedMember] = { "expected member", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedStatement] = { "expected statement", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedParameterPort] = { "expected parameter declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedNonAnsiPort] = { "expected non-ansi port declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedAnsiPort] = { "expected ansi port declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedModportPort] = { "expected modport item port declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedFunctionPort] = { "expected subroutine port declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedAssertionItemPort] = { "expected assertion item construct port declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedForInitializer] = { "expected for loop initializer", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedExpression] = { "expected expression", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedOpenRangeElement] = { "expected open range element", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedStreamExpression] = { "expected stream expression", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedArgument] = { "expected argument", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedVariableDeclarator] = { "expected variable declarator", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedConditionalPattern] = { "expected conditional pattern", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedAttribute] = { "expected attribute", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedPackageImport] = { "expected package import", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedHierarchicalInstantiation] = { "expected hierarhical instantiation", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedPortConnection] = { "expected port connection", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedVectorDigits] = { "expected vector literal digits", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedVariableAssignment] = { "expected variable assignment", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedInterfaceClassName] = { "expected interface class name", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedAssignmentKey] = { "expected assignment key", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedDistItem] = { "expected dist item", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedIfOrCase] = { "expected 'if' or 'case' after '{}' keyword", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedClassScope] = { "expected class scope before new keyword", DiagnosticSeverity::Error };
    descriptors[DiagCode::NoLabelOnSemicolon] = { "labels are not allowed on empty semicolon", DiagnosticSeverity::Error };
    descriptors[DiagCode::DeferredDelayMustBeZero] = { "deferred assertion delay must be zero", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidGenvarIterExpression] = { "invalid genvar iteration expression", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedGenvarIterVar] = { "expected genvar iteration variable", DiagnosticSeverity::Error };
    descriptors[DiagCode::ConstFunctionPortRequiresRef] = { "'const' in subroutine formal port requires 'ref' direction specifier", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedClockingSkew] = { "expected clocking skew", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpectedDPISpecString] = { "expected DPI spec string", DiagnosticSeverity::Error };
    descriptors[DiagCode::AttributesOnEmpty] = { "attributes are not allowed on an empty item", DiagnosticSeverity::Error };
    descriptors[DiagCode::AttributesOnClassParam] = { "attributes are not allowed on a class parameter", DiagnosticSeverity::Error };
    descriptors[DiagCode::AttributesOnGenerateRegion] = { "attributes are not allowed on a generate region", DiagnosticSeverity::Error };
    descriptors[DiagCode::AttributesOnTimeDecl] = { "attributes are not allowed on a time units declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::ParseTreeTooDeep] = { "language constructs are too deeply nested", DiagnosticSeverity::Error };

    // declarations
    descriptors[DiagCode::NotePreviousDefinition] = { "previous definition here", DiagnosticSeverity::Note };
    descriptors[DiagCode::LocalParamNoInitializer] = { "local parameter is missing an initializer", DiagnosticSeverity::Error };
    descriptors[DiagCode::BodyParamNoInitializer] = { "parameter declaration is missing an initializer", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidDimensionRange] = { "invalid dimension range", DiagnosticSeverity::Error };
    descriptors[DiagCode::DimensionRequiresConstRange] = { "dimension requires a constant range", DiagnosticSeverity::Error };
    descriptors[DiagCode::PackedDimsRequireFullRange] = { "packed dimensions require a full range specification", DiagnosticSeverity::Error };
    descriptors[DiagCode::PackedDimsOnPredefinedType] = { "packed dimensions not allowed on predefined integer type '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::MixingOrderedAndNamedParams] = { "mixing ordered and named parameter assignments is not allowed", DiagnosticSeverity::Error };
    descriptors[DiagCode::DuplicateParamAssignment] = { "duplicate assignment for parameter '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::NotePreviousUsage] = { "previous usage here", DiagnosticSeverity::Note };
    descriptors[DiagCode::ParamHasNoValue] = { "instance of module '{}' does not provide a value for parameter '{}' and it does not have a default value", DiagnosticSeverity::Error };
    descriptors[DiagCode::NoteDeclarationHere] = { "declared here", DiagnosticSeverity::Note };
    descriptors[DiagCode::TooManyParamAssignments] = { "too many parameter assignments given to instantiation of module '{}' ({} given, expected {})", DiagnosticSeverity::Error };
    descriptors[DiagCode::AssignedToLocalPortParam] = { "can't assign a value to a localparam", DiagnosticSeverity::Error };
    descriptors[DiagCode::AssignedToLocalBodyParam] = { "can't assign a value to a localparam (parameters in the body of a module are implicitly local when you have a parameter port list)", DiagnosticSeverity::Error };
    descriptors[DiagCode::ParameterDoesNotExist] = { "parameter '{}' does not exist in module '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::DuplicateAttribute] = { "duplicate attribute definition '{}'; taking last value", DiagnosticSeverity::Warning };
    descriptors[DiagCode::PackedMemberNotIntegral] = { "packed members must be of integral type (type is {})", DiagnosticSeverity::Error };
    descriptors[DiagCode::PackedMemberHasInitializer] = { "packed members can not have initializers", DiagnosticSeverity::Error };
    descriptors[DiagCode::Redefinition] = { "redefinition of '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::RedefinitionDifferentType] = { "redefinition of '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::RedefinitionDifferentType] = { "redefinition of '{}' with a different type: {} vs {}", DiagnosticSeverity::Error };
    descriptors[DiagCode::RedefinitionDifferentSymbolKind] = { "redefinition of '{}' as different kind of symbol", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnresolvedForwardTypedef] = { "forward typedef '{}' does not resolve to a data type", DiagnosticSeverity::Error };
    descriptors[DiagCode::ForwardTypedefDoesNotMatch] = { "forward typedef basic type '{}' does not match declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::PortTypeNotInterfaceOrData] = { "port type '{}' is neither an interface nor a data type", DiagnosticSeverity::Error };
    descriptors[DiagCode::VarWithInterfacePort] = { "'var' keyword may not be used with an interface port", DiagnosticSeverity::Error };
    descriptors[DiagCode::DirectionWithInterfacePort] = { "port direction not allowed on an interface port", DiagnosticSeverity::Error };
    descriptors[DiagCode::InOutPortCannotBeVariable] = { "variable port '{}' cannot have direction inout", DiagnosticSeverity::Error };
    descriptors[DiagCode::RefPortMustBeVariable] = { "ref port '{}' cannot be of net type", DiagnosticSeverity::Error };
    descriptors[DiagCode::MissingPortIODeclaration] = { "port '{}' has no I/O member declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::CantDeclarePortSigned] = { "port '{}' cannot be declared signed because its type {} is not integral", DiagnosticSeverity::Error };
    descriptors[DiagCode::PortDeclDimensionsMismatch] = { "dimensions of port '{}' do not match its declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnknownPackage] = { "unknown package '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::MixingOrderedAndNamedPorts] = { "mixing ordered and named port connections is not allowed", DiagnosticSeverity::Error };
    descriptors[DiagCode::DuplicateWildcardPortConnection] = { "duplicate wildcard port connection", DiagnosticSeverity::Error };
    descriptors[DiagCode::DuplicatePortConnection] = { "duplicate connection for port '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::TooManyPortConnections] = { "too many port connections given to instantiation of module '{}' ({} given, expected {})", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnconnectedNamedPort] = { "port '{}' has no connection", DiagnosticSeverity::Warning };
    descriptors[DiagCode::PortDoesNotExist] = { "port '{}' does not exist in module '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::InterfacePortNotConnected] = { "interface port '{}' not connected", DiagnosticSeverity::Error };
    descriptors[DiagCode::InterfacePortInvalidExpression] = { "invalid expression for interface port '{}'", DiagnosticSeverity::Error };

    // expressions
    descriptors[DiagCode::BadUnaryExpression] = { "invalid operand type {} to unary expression", DiagnosticSeverity::Error };
    descriptors[DiagCode::BadBinaryExpression] = { "invalid operands to binary expression ({} and {})", DiagnosticSeverity::Error };
    descriptors[DiagCode::BadIndexExpression] = { "value of type {} cannot be indexed", DiagnosticSeverity::Error };
    descriptors[DiagCode::BadConcatExpression] = { "invalid operand type {} in concatenation", DiagnosticSeverity::Error };
    descriptors[DiagCode::CannotIndexScalar] = { "scalar type cannot be indexed", DiagnosticSeverity::Error };
    descriptors[DiagCode::IndexMustBeIntegral] = { "index expression must be integral", DiagnosticSeverity::Error };
    descriptors[DiagCode::BadAssignment] = { "value of type {} cannot be assigned to type {}", DiagnosticSeverity::Error };
    descriptors[DiagCode::NoImplicitConversion] = { "no implicit conversion from {} to {}; explicit conversion exists, are you missing a cast?", DiagnosticSeverity::Error };
    descriptors[DiagCode::TooManyArguments] = { "too many arguments to subroutine call; expected {} but {} were provided", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpressionNotAssignable] = { "expression is not assignable", DiagnosticSeverity::Error };
    descriptors[DiagCode::ReplicationZeroOutsideConcat] = { "replication constant can only be zero inside of a concatenation", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidMemberAccess] = { "invalid member access for type {}", DiagnosticSeverity::Error };
    descriptors[DiagCode::ExpressionNotCallable] = { "expression is not callable", DiagnosticSeverity::Error };

    // statements
    descriptors[DiagCode::ReturnNotInSubroutine] = { "return statement is only valid inside task and function blocks", DiagnosticSeverity::Error };

    // types
    descriptors[DiagCode::InvalidEnumBase] = { "", DiagnosticSeverity::Error };
    descriptors[DiagCode::NetTypeNotAllowed] = { "{} is a net type, not a data type", DiagnosticSeverity::Error };

    // lookups
    descriptors[DiagCode::AmbiguousWildcardImport] = { "multiple imports found for identifier '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::NoteImportedFrom] = { "imported from here", DiagnosticSeverity::Note };
    descriptors[DiagCode::ImportNameCollision] = { "import of '{}' collides with an existing declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::UndeclaredIdentifier] = { "use of undeclared identifier '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnknownClassOrPackage] = { "unknown class or package '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::UsedBeforeDeclared] = { "identifier '{}' used before its declaration", DiagnosticSeverity::Error };
    descriptors[DiagCode::NotAType] = { "'{}' is not a type", DiagnosticSeverity::Error };
    descriptors[DiagCode::NotAValue] = { "'{}' does not refer to a value", DiagnosticSeverity::Error };
    descriptors[DiagCode::NotAHierarchicalScope] = { "'{}' is not a hierarchical scope name", DiagnosticSeverity::Error };
    descriptors[DiagCode::NotAModport] = { "'{}' is not a modport", DiagnosticSeverity::Error };
    descriptors[DiagCode::NotAnInterface] = { "'{}' is not an interface or modport", DiagnosticSeverity::Error };
    descriptors[DiagCode::HierarchicalNotAllowedInConstant] = { "hierarchical names are not allowed in constant expressions", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnknownMember] = { "no member named '{}' in {}", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnknownPackageMember] = { "no member named '{}' in package '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnknownUnitMember] = { "no member named '{}' in compilation unit", DiagnosticSeverity::Error };
    descriptors[DiagCode::RecursiveDefinition] = { "'{}' recursively depends on its own definition", DiagnosticSeverity::Error };
    descriptors[DiagCode::ImplicitNamedPortNotFound] = { "could not find connection for implicit named port '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::ImplicitNamedPortTypeMismatch] = { "implicit named port '{}' of type {} connects to value of inequivalent type {}", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnexpectedSystemName] = { "unexpected use of system name", DiagnosticSeverity::Error };
    descriptors[DiagCode::UnknownSystemMethod] = { "unknown built-in method '{}'", DiagnosticSeverity::Error };
    descriptors[DiagCode::ScopeNotIndexable] = { "hierarchical scope '{}' is not indexable", DiagnosticSeverity::Error };
    descriptors[DiagCode::InvalidScopeIndexExpression] = { "invalid hierarchical index expression", DiagnosticSeverity::Error };
    descriptors[DiagCode::ScopeIndexOutOfRange] = { "hierarchical index {} is out of scope's declared range", DiagnosticSeverity::Error };
    descriptors[DiagCode::CouldNotResolveHierarchicalPath] = { "could not resolve hierarchical path name '{}'", DiagnosticSeverity::Error };

    // constant evaluation
    descriptors[DiagCode::ExpressionNotConstant] = { "expression is not constant", DiagnosticSeverity::Error };
    descriptors[DiagCode::NoteInCallTo] = { "in call to '{}'", DiagnosticSeverity::Note };
    descriptors[DiagCode::NoteNonConstVariable] = { "reference to non-constant variable '{}' is not allowed in a constant expression", DiagnosticSeverity::Note };
    descriptors[DiagCode::NoteArrayIndexInvalid] = { "cannot refer to element {} of array of type {} in a constant expression", DiagnosticSeverity::Note };
    descriptors[DiagCode::NotePartSelectInvalid] = { "cannot select range of {}:{} from array of type {} in a constant expression", DiagnosticSeverity::Note };
    descriptors[DiagCode::NoteHierarchicalNameInCE] = { "reference to '{}' by hierarchical name is not allowed in a constant expression", DiagnosticSeverity::Note };
    descriptors[DiagCode::NoteFunctionIdentifiersMustBeLocal] = { "all identifiers that are not parameters must be declared locally to a constant function", DiagnosticSeverity::Note };
    descriptors[DiagCode::NoteParamUsedInCEBeforeDecl] = { "parameter '{}' is declared after the invocation of the current constant function", DiagnosticSeverity::Note };

    descriptors[DiagCode::NotYetSupported] = { "language feature not yet supported", DiagnosticSeverity::Error };
    // clang-format on

    // if this assert fails, you added a new diagnostic without adding a descriptor for it
    ASSERT((int)DiagCode::MaxValue == descriptors.size());
}

void DiagnosticWriter::setMessage(DiagCode code, std::string format) {
    descriptors[code].format = std::move(format);
}

void DiagnosticWriter::setSeverity(DiagCode code, DiagnosticSeverity severity) {
    descriptors[code].severity = severity;
}

DiagnosticSeverity DiagnosticWriter::getSeverity(DiagCode code) const {
    auto it = descriptors.find(code);
    if (it == descriptors.end())
        throw std::logic_error("Invalid diagnostic code");
    return it->second.severity;
}

static void getMacroArgExpansions(const SourceManager& sm, SourceLocation loc, bool isStart,
                                  SmallVector<BufferID>& results) {
    while (sm.isMacroLoc(loc)) {
        if (sm.isMacroArgLoc(loc)) {
            results.append(loc.buffer());
            loc = sm.getOriginalLoc(loc);
        }
        else {
            auto range = sm.getExpansionRange(loc);
            loc = isStart ? range.start() : range.end();
        }
    }
}

static void getCommonMacroArgExpansions(const SourceManager& sm, SourceLocation start,
                                        SourceLocation end, std::vector<BufferID>& results) {
    SmallVectorSized<BufferID, 8> startArgExpansions;
    SmallVectorSized<BufferID, 8> endArgExpansions;
    getMacroArgExpansions(sm, start, true, startArgExpansions);
    getMacroArgExpansions(sm, end, false, endArgExpansions);
    std::stable_sort(startArgExpansions.begin(), startArgExpansions.end());
    std::stable_sort(endArgExpansions.begin(), endArgExpansions.end());

    std::set_intersection(startArgExpansions.begin(), startArgExpansions.end(),
                          endArgExpansions.begin(), endArgExpansions.end(),
                          std::back_inserter(results));
}

static SourceLocation getMatchingMacroLoc(const SourceManager& sm, SourceLocation loc,
                                          SourceLocation contextLoc, bool isStart,
                                          span<const BufferID> commonArgs) {
    if (loc.buffer() == contextLoc.buffer())
        return loc;

    if (!sm.isMacroLoc(loc))
        return {};

    SourceRange macroRange;
    SourceRange macroArgRange;
    if (sm.isMacroArgLoc(loc)) {
        // Only look at the original location of this argument if the other location
        // in the range is also present in the expansion.
        if (std::binary_search(commonArgs.begin(), commonArgs.end(), loc.buffer())) {
            SourceLocation orig = sm.getOriginalLoc(loc);
            macroRange = SourceRange(orig, orig);
        }
        macroArgRange = sm.getExpansionRange(loc);
    }
    else {
        macroRange = sm.getExpansionRange(loc);

        SourceLocation orig = sm.getOriginalLoc(loc);
        macroArgRange = SourceRange(orig, orig);
    }

    SourceLocation macroLoc = isStart ? macroRange.start() : macroRange.end();
    if (macroLoc) {
        macroLoc = getMatchingMacroLoc(sm, macroLoc, contextLoc, isStart, commonArgs);
        if (macroLoc)
            return macroLoc;
    }

    SourceLocation argLoc = isStart ? macroArgRange.start() : macroArgRange.end();
    return getMatchingMacroLoc(sm, argLoc, contextLoc, isStart, commonArgs);
}

static void mapDiagnosticRanges(const SourceManager& sm, SourceLocation loc,
                                span<const SourceRange> ranges, SmallVector<SourceRange>& mapped) {
    for (auto& range : ranges) {
        SourceLocation start = range.start();
        SourceLocation end = range.end();

        SmallMap<BufferID, SourceLocation, 8> startMap;
        while (sm.isMacroLoc(start) && start.buffer() != end.buffer()) {
            startMap[start.buffer()] = start;
            start = sm.getExpansionLoc(start);
        }

        if (start.buffer() != end.buffer()) {
            while (sm.isMacroLoc(end) && !startMap.count(end.buffer()))
                end = sm.getExpansionRange(end).end();

            if (sm.isMacroLoc(end))
                start = startMap[end.buffer()];
        }

        // We now have a common macro location; find common argument expansions.
        std::vector<BufferID> commonArgs;
        getCommonMacroArgExpansions(sm, start, end, commonArgs);

        start = getMatchingMacroLoc(sm, start, loc, true, commonArgs);
        end = getMatchingMacroLoc(sm, end, loc, false, commonArgs);
        if (!start || !end)
            continue;

        start = sm.getFullyOriginalLoc(start);
        end = sm.getFullyOriginalLoc(end);
        mapped.emplace(start, end);
    }
}

static bool checkMacroArgRanges(const SourceManager& sm, SourceLocation loc,
                                span<const SourceRange> ranges) {
    if (!sm.isMacroArgLoc(loc))
        return false;

    SmallVectorSized<SourceRange, 8> mappedRanges;
    mapDiagnosticRanges(sm, loc, ranges, mappedRanges);

    if (ranges.size() > mappedRanges.size())
        return false;

    loc = sm.getExpansionLoc(loc);

    for (auto& range : mappedRanges) {
        if (!sm.isMacroArgLoc(range.start()) || !sm.isMacroArgLoc(range.end()))
            return false;

        if (sm.getExpansionLoc(range.start()) != loc || sm.getExpansionLoc(range.end()) != loc)
            return false;
    }

    return true;
}

std::string DiagnosticWriter::report(const Diagnostic& diagnostic) {
    // walk out until we find a location for this diagnostic that isn't inside a macro
    SmallVectorSized<SourceLocation, 8> expansionLocs;
    SourceLocation location = diagnostic.location;
    size_t ignoreUntil = 0;

    while (sourceManager.isMacroLoc(location)) {
        SourceLocation prevLoc = location;
        if (sourceManager.isMacroArgLoc(location)) {
            expansionLocs.append(sourceManager.getExpansionLoc(location));
            location = sourceManager.getOriginalLoc(location);
        }
        else {
            expansionLocs.append(location);
            location = sourceManager.getExpansionLoc(location);
        }

        if (checkMacroArgRanges(sourceManager, prevLoc, diagnostic.ranges))
            ignoreUntil = expansionLocs.size();
    }

    // build the error message from arguments, if we have any
    FormatBuffer buffer;
    Descriptor& desc = descriptors[diagnostic.code];
    std::string message;

    if (diagnostic.args.empty()) {
        message = desc.format;
    }
    else {
        // The fmtlib API for arg lists isn't very pretty, but it gets the job done
        using ctx = fmt::format_context;
        std::vector<fmt::basic_format_arg<ctx>> args;
        for (auto& arg : diagnostic.args)
            args.push_back(fmt::internal::make_arg<ctx>(arg));

        message = fmt::vformat(desc.format,
                               fmt::basic_format_args<ctx>(args.data(), (unsigned)args.size()));
    }

    SmallVectorSized<SourceRange, 8> mappedRanges;
    mapDiagnosticRanges(sourceManager, location, diagnostic.ranges, mappedRanges);
    formatDiag(buffer, location, mappedRanges, severityToString[(int)desc.severity], message);

    // write out macro expansions, if we have any
    size_t index = 0;
    while (!expansionLocs.empty()) {
        location = expansionLocs.back();
        expansionLocs.pop();
        index++;

        if (index <= ignoreUntil)
            continue;

        std::string name{ sourceManager.getMacroName(location) };
        if (name.empty())
            name = "expanded from here";
        else
            name = "expanded from macro '" + name + "'";

        SmallVectorSized<SourceRange, 8> macroRanges;
        mapDiagnosticRanges(sourceManager, location, diagnostic.ranges, macroRanges);
        formatDiag(buffer, sourceManager.getFullyOriginalLoc(location), macroRanges, "note", name);
    }

    for (const Diagnostic& note : diagnostic.notes)
        buffer.append(report(note));

    return buffer.str();
}

std::string DiagnosticWriter::report(const Diagnostics& diagnostics) {
    std::deque<SourceLocation> includeStack;
    BufferID lastBuffer;
    FormatBuffer buffer;

    for (auto& diag : diagnostics) {
        SourceLocation loc = sourceManager.getFullyExpandedLoc(diag.location);
        if (loc.buffer() != lastBuffer) {
            // We're looking at diagnostics from another file now. See if we should print
            // include stack info before we go on with the reports.
            lastBuffer = loc.buffer();
            getIncludeStack(lastBuffer, includeStack);

            for (auto& includeLoc : includeStack) {
                buffer.format("in file included from {}:{}:\n",
                              sourceManager.getFileName(includeLoc),
                              sourceManager.getLineNumber(includeLoc));
            }
        }
        buffer.append(report(diag));
    }
    return buffer.str();
}

string_view DiagnosticWriter::getBufferLine(SourceLocation location, uint32_t col) {
    string_view text = sourceManager.getSourceText(location.buffer());
    if (text.empty())
        return "";

    const char* start = text.data() + location.offset() - (col - 1);
    const char* curr = start;
    while (*curr != '\n' && *curr != '\r' && *curr != '\0')
        curr++;

    return string_view(start, (uint32_t)(curr - start));
}

void DiagnosticWriter::getIncludeStack(BufferID buffer, std::deque<SourceLocation>& stack) {
    stack.clear();
    while (buffer) {
        SourceLocation loc = sourceManager.getIncludedFrom(buffer);
        if (!loc.buffer())
            break;

        stack.push_front(loc);
        buffer = loc.buffer();
    }
}

void DiagnosticWriter::highlightRange(SourceRange range, SourceLocation caretLoc, uint32_t col,
                                      string_view sourceLine, std::string& buffer) {
    // Trim the range so that it only falls on the same line as the cursor
    uint32_t start = range.start().offset();
    uint32_t end = range.end().offset();
    uint32_t startOfLine = caretLoc.offset() - (col - 1);
    uint32_t endOfLine = startOfLine + (uint32_t)sourceLine.length();
    if (start < startOfLine)
        start = startOfLine;
    if (end > endOfLine)
        end = endOfLine;

    if (start >= end)
        return;

    // walk the range in to skip any leading or trailing whitespace
    start -= startOfLine;
    end -= startOfLine;
    while (sourceLine[start] == ' ' || sourceLine[start] == '\t') {
        start++;
        if (start == end)
            return;
    }
    while (sourceLine[end - 1] == ' ' || sourceLine[end - 1] == '\t') {
        end--;
        if (start == end)
            return;
    }

    // finally add the highlight chars
    for (; start != end; start++)
        buffer[start] = '~';
}

template<typename T>
void DiagnosticWriter::formatDiag(T& buffer, SourceLocation loc, span<const SourceRange> ranges,
                                  const char* severity, const std::string& msg) {
    uint32_t col = sourceManager.getColumnNumber(loc);
    buffer.format("{}:{}:{}: {}: {}", sourceManager.getFileName(loc),
                  sourceManager.getLineNumber(loc), col, severity, msg);

    string_view line = getBufferLine(loc, col);
    if (!line.empty()) {
        buffer.format("\n{}\n", line);

        // Highlight any ranges and print the caret location.
        std::string highlight(std::max(line.length(), (size_t)col), ' ');

        // handle tabs to get proper alignment on a terminal
        for (uint32_t i = 0; i < line.length(); ++i) {
            if (line[i] == '\t')
                highlight[i] = '\t';
        }

        for (SourceRange range : ranges)
            highlightRange(range, loc, col, line, highlight);

        highlight[col - 1] = '^';
        highlight.erase(highlight.find_last_not_of(' ') + 1);
        buffer.append(highlight);
    }
    buffer.append("\n");
}

} // namespace slang
