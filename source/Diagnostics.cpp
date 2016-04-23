#include <cstdint>
#include <memory>
#include <string>
#include <vector>
#include <deque>
#include <unordered_map>
#include <set>
#include <algorithm>
#include <filesystem>

#include "../external/cppformat/format.h"

#include "Buffer.h"
#include "StringRef.h"
#include "Diagnostics.h"
#include "SourceManager.h"

namespace slang {

struct DiagnosticDescriptor {
	StringRef format;
	DiagnosticSeverity severity;

	DiagnosticDescriptor(StringRef format) :
		format(format), severity(DiagnosticSeverity::Error)
	{
	}
};

static const char* severityToString[] = {
	"info",
	"warning",
	"error"
};

static const DiagnosticDescriptor diagnosticDescriptors[] = {
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

static StringRef getBufferLine(SourceManager& sourceManager, SourceLocation location, uint32_t col);

Diagnostics::Diagnostics() :
	Buffer::Buffer(128)
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

std::string DiagnosticReport::toString(SourceManager& sourceManager) const {
	auto location = diagnostic.location;
	uint32_t col = sourceManager.getColumnNumber(location);

	fmt::MemoryWriter writer;
	writer.write("{}:{}:{}: {}: {}",
		sourceManager.getFileName(location.file),
		sourceManager.getLineNumber(location),
		col,
		severityToString[(int)severity],
		format
	);

	// print out the source line, if possible
	StringRef line = getBufferLine(sourceManager, location, col);
	if (!line)
		writer << '\n';
	else {
		writer.write("\n{}\n", line);
		for (int i = 0; i < col - 1; i++) {
			if (line[i] == '\t')
				writer << '\t';
			else
				writer << ' ';
		}
		writer << '^';
	}

	return writer.str();
}

StringRef getBufferLine(SourceManager& sourceManager, SourceLocation location, uint32_t col) {
	auto buffer = sourceManager.getBuffer(location.file);
	if (!buffer)
		return nullptr;

	const char* start = buffer->data.begin() + location.offset - (col - 1);
	uint32_t len = 0;
	while (start[len] != '\n' && start[len] != '\r')
		len++;

	return StringRef(start, len);
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