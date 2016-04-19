#pragma once

namespace slang {

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
    MissingExponentDigits,
    MissingFractionalDigits,
    OctalEscapeCodeTooBig,
    InvalidHexEscapeCode,
    UnknownEscapeCode,
    RealExponentTooLarge,
    SignedLiteralTooLarge,
    IntegerSizeZero,
    IntegerSizeTooLarge,
    MissingVectorBase,
    MissingVectorDigits,
    ExpectedIncludeFileName,

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
    ImplicitNotAllowed,
    MultipleTypesInDeclaration,
    DirectionOnInterfacePort,
    ColonShouldBeDot

};

std::ostream& operator<<(std::ostream& os, DiagCode code);

class Diagnostic {
public:
    DiagCode code;
    int location;
    int width;

	Diagnostic(DiagCode code, int location, int width) :
		code(code), location(location), width(width)
	{
    }
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

	DiagnosticReport(const Diagnostic& diagnostic, StringRef format, DiagnosticSeverity severity) :
		diagnostic(diagnostic), format(format), severity(severity)
	{
	}

	std::string toString() const;
};

class Diagnostics : public Buffer<Diagnostic> {
public:
    Diagnostics();

	DiagnosticReport getReport(const Diagnostic& diagnostic) const;
};

}