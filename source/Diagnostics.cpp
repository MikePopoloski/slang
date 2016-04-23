#include <cstdint>
#include <memory>
#include <string>
#include <algorithm>

#include "Buffer.h"
#include "StringRef.h"
#include "Diagnostics.h"

namespace slang {

struct DiagnosticDescriptor {
	StringRef format;
	DiagnosticSeverity severity;

	DiagnosticDescriptor(StringRef format) :
		format(format), severity(DiagnosticSeverity::Error)
	{
	}
};

const static DiagnosticDescriptor diagnosticDescriptors[] = {
	// lexer
	{ "Non-printable character in source text. SystemVerilog only supports ASCII text." },
	{ "UTF-8 sequence in source text. SystemVerilog only supports ASCII text." },
	{ "Unicode BOM at start of source text. SystemVerilog only supports ASCII text." },
	{ "Embedded NUL in source text. Are you sure this is source code?" },
	{ "Expected directive name." },
	{ "Expected newline after escape sequence; remove trailing whitespace." },
	{ "Missing closing quote." },
	{ "Block comment unclosed at end of file." },
	{ "Nested block comments are disallowed by SystemVerilog." },
	{ "Block comments on the same line as a directive must also be terminated on that line." },
	{ "Expected exponent digits." },
	{ "Expected fractional digits." },
	{ "Octal escape code is too large to be an ASCII character." },
	{ "Invalid hexadecimal number." },
	{ "Unknown character escape sequence." },
	{ "Literal exponent is too large." },
	{ "Signed integer constant is too large." },
	{ "Vector literal cannot have a size of zero." },
	{ "Vector literal is too large." },
	{ "Unknown vector literal base specifier." },
	{ "Expected vector literal digits." },
	{ "Expected an include file name." },
	
	// preprocessor
	{ "CouldNotOpenIncludeFile" },
	{ "ExceededMaxIncludeDepth" },
	{ "UnknownDirective" },
	{ "ExpectedEndOfDirective" },
	{ "ExpectedEndOfMacroArgs" },
	{ "ExpectedEndIfDirective" },
	{ "UnexpectedDirective" },
	{ "UnbalancedMacroArgDims" },
	{ "ExpectedMacroArgs" },

	// parser
	{ "SyntaxError" },
	{ "ImplicitNotAllowed" },
	{ "MultipleTypesInDeclaration" },
	{ "DirectionOnInterfacePort" },
	{ "ColonShouldBeDot" }
};

Diagnostics::Diagnostics(SourceManager& sourceManager) :
	Buffer::Buffer(128),
	sourceManager(sourceManager)
{
}

DiagnosticReport Diagnostics::getReport(const Diagnostic& diagnostic) const {
	auto& descriptor = diagnosticDescriptors[(int)diagnostic.code];
	return {
		diagnostic,
		descriptor.format,
		descriptor.severity
	};
}

std::string DiagnosticReport::toString() const {
	std::string result;
	result += std::to_string(diagnostic.location.file.id) + ":" +
			  std::to_string(diagnostic.location.offset) + ": ";

	switch (severity) {
		case DiagnosticSeverity::Error: result += "error: "; break;
		case DiagnosticSeverity::Warning: result += "warning: "; break;
		case DiagnosticSeverity::Info: result += "info: "; break;
	}
	return result + format.toString();
}

std::ostream& operator<<(std::ostream& os, DiagCode code) {
#define CASE(name) case DiagCode::name: os << #name; break
	switch (code) {
		CASE(NonPrintableChar);
		CASE(UTF8Char);
		CASE(UnicodeBOM);
		CASE(EmbeddedNull);
		CASE(MisplacedDirectiveChar);
		CASE(EscapedWhitespace);
		CASE(ExpectedClosingQuote);
		CASE(UnterminatedBlockComment);
		CASE(NestedBlockComment);
		CASE(SplitBlockCommentInDirective);
		CASE(MissingExponentDigits);
		CASE(MissingFractionalDigits);
		CASE(OctalEscapeCodeTooBig);
		CASE(InvalidHexEscapeCode);
		CASE(UnknownEscapeCode);
		CASE(RealExponentTooLarge);
		CASE(SignedLiteralTooLarge);
		CASE(IntegerSizeZero);
		CASE(IntegerSizeTooLarge);
		CASE(MissingVectorBase);
		CASE(MissingVectorDigits);
		CASE(ExpectedIncludeFileName);
		CASE(CouldNotOpenIncludeFile);
		CASE(ExceededMaxIncludeDepth);
		CASE(UnknownDirective);
		CASE(ExpectedEndOfDirective);
		CASE(ExpectedEndOfMacroArgs);
		CASE(ExpectedEndIfDirective);
		CASE(UnexpectedDirective);
		CASE(UnbalancedMacroArgDims);
		CASE(ExpectedMacroArgs);
		CASE(SyntaxError);
		CASE(ImplicitNotAllowed);
		CASE(MultipleTypesInDeclaration);
		CASE(DirectionOnInterfacePort);
		CASE(ColonShouldBeDot);
		default: ASSERT(false && "Missing case");
	}
	return os;
#undef CASE
}

}