#include <cstdint>
#include <memory>
#include <string>
#include <algorithm>

#include "Buffer.h"
#include "StringRef.h"
#include "Diagnostics.h"

namespace slang {

const static StringRef diagnosticDescriptors[] = {
	// lexer
	"NonPrintableChar",
	"UTF8Char",
	"UnicodeBOM",
	"EmbeddedNull",
	"MisplacedDirectiveChar",
	"EscapedWhitespace",
	"NewlineInStringLiteral",
	"UnterminatedStringLiteral",
	"UnterminatedBlockComment",
	"NestedBlockComment",
	"SplitBlockCommentInDirective",
	"MissingExponentDigits",
	"MissingFractionalDigits",
	"OctalEscapeCodeTooBig",
	"InvalidHexEscapeCode",
	"UnknownEscapeCode",
	"RealExponentTooLarge",
	"SignedLiteralTooLarge",
	"IntegerSizeZero",
	"IntegerSizeTooLarge",
	"MissingVectorBase",
	"MissingVectorDigits",
	"ExpectedEndOfIncludeFileName",
	"ExpectedIncludeFileName",

	// preprocessor
	"CouldNotOpenIncludeFile",
	"ExceededMaxIncludeDepth",
	"UnknownDirective",
	"ExpectedEndOfDirective",
	"ExpectedEndOfMacroArgs",
	"ExpectedEndIfDirective",
	"UnexpectedDirective",
	"UnbalancedMacroArgDims",
	"ExpectedMacroArgs",

	// parser
	"SyntaxError",
	"ImplicitNotAllowed",
	"MultipleTypesInDeclaration",
	"DirectionOnInterfacePort",
	"ColonShouldBeDot"
};

Diagnostics::Diagnostics() :
	Buffer::Buffer(128)
{
}

DiagnosticReport Diagnostics::getReport(const Diagnostic& diagnostic) const {
	return DiagnosticReport(diagnostic, diagnosticDescriptors[(int)diagnostic.code]);
}

std::string DiagnosticReport::toString() const {
	return format.toString();
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
		CASE(NewlineInStringLiteral);
		CASE(UnterminatedStringLiteral);
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
		CASE(ExpectedEndOfIncludeFileName);
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