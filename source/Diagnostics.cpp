//------------------------------------------------------------------------------
// Diagnostics.cpp
// Diagnostic tracking and reporting.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Diagnostics.h"

#include <algorithm>

#include "../external/fmt/format.h"
#include "../external/fmt/ostream.h"

#include "SourceManager.h"

namespace slang {

static const char* severityToString[] = {
    "info",
    "warning",
    "error"
};

Diagnostic::Diagnostic(DiagCode code, SourceLocation location) :
    code(code), location(location)
{
}

Diagnostic& operator<<(Diagnostic& diag, Diagnostic::Arg&& arg) {
    diag.args.push_back(std::move(arg));
    return diag;
}

std::ostream& operator<<(std::ostream& os, const Diagnostic::Arg& arg) {
    return apply([&](auto&& t) -> auto& { return os << t; }, arg);
}

Diagnostics::Diagnostics() :
    Buffer::Buffer(8)
{
}

Diagnostic& Diagnostics::add(DiagCode code, SourceLocation location) {
    emplace(code, location);
    return back();
}

DiagnosticWriter::DiagnosticWriter(SourceManager& sourceManager) :
	sourceManager(sourceManager)
{
	Descriptor* d = descriptors;
	// lexer
	*d++ = { "non-printable character in source text; SystemVerilog only supports ASCII text", DiagnosticSeverity::Error };
	*d++ = { "UTF-8 sequence in source text; SystemVerilog only supports ASCII text", DiagnosticSeverity::Error };
	*d++ = { "Unicode BOM at start of source text; SystemVerilog only supports ASCII text", DiagnosticSeverity::Error };
	*d++ = { "embedded NUL in source text; are you sure this is source code?", DiagnosticSeverity::Error };
	*d++ = { "expected directive name", DiagnosticSeverity::Error };
	*d++ = { "unexpected whitespace after escape character", DiagnosticSeverity::Error };
	*d++ = { "missing closing quote", DiagnosticSeverity::Error };
	*d++ = { "block comment unclosed at end of file", DiagnosticSeverity::Error };
	*d++ = { "nested block comments are disallowed by SystemVerilog", DiagnosticSeverity::Error };
	*d++ = { "block comments on the same line as a directive must also be terminated on that line", DiagnosticSeverity::Error };
	*d++ = { "expected integer base specifier after signed specifier", DiagnosticSeverity::Error };
	*d++ = { "expected fractional digits after decimal", DiagnosticSeverity::Error };
	*d++ = { "octal escape code is too large to be an ASCII character", DiagnosticSeverity::Error };
	*d++ = { "invalid hexadecimal number", DiagnosticSeverity::Error };
	*d++ = { "unknown character escape sequence", DiagnosticSeverity::Error };
	*d++ = { "expected an include file name", DiagnosticSeverity::Error };
	*d++ = { "expected exponent digits", DiagnosticSeverity::Error };
	*d++ = { "vector literals must not start with a leading underscore", DiagnosticSeverity::Error };
	*d++ = { "decimal literals cannot have multiple X or Z digits", DiagnosticSeverity::Error };
	*d++ = { "expected binary digit", DiagnosticSeverity::Error };
	*d++ = { "expected octal digit", DiagnosticSeverity::Error };
	*d++ = { "expected decimal digit", DiagnosticSeverity::Error };
	*d++ = { "expected hexadecimal digit", DiagnosticSeverity::Error };

	// numeric
	*d++ = { "size of vector literal cannot be zero", DiagnosticSeverity::Error };
	*d++ = { "size of vector literal is too large (> {} bits)", DiagnosticSeverity::Error };
	*d++ = { "real literal overflows 64 bits", DiagnosticSeverity::Error };
	*d++ = { "signed integer overflows 32 bits", DiagnosticSeverity::Error };
	*d++ = { "decimal literal overflows 32 bits", DiagnosticSeverity::Error };
	*d++ = { "literal specifies too many digits for the given number of bits", DiagnosticSeverity::Error };

	// preprocessor
	*d++ = { "could not find or open include file", DiagnosticSeverity::Error };
	*d++ = { "exceeded max include depth", DiagnosticSeverity::Error };
	*d++ = { "unknown macro or compiler directive", DiagnosticSeverity::Error };
	*d++ = { "expected end of directive (missing newline?)", DiagnosticSeverity::Error };
	*d++ = { "expected end of macro arguments (missing closing parenthesis?)", DiagnosticSeverity::Error };
	*d++ = { "unexpected conditional directive", DiagnosticSeverity::Error };
	*d++ = { "unbalanced macro argument delimiters ((), [], or {{}}); didn't see an end '{}'", DiagnosticSeverity::Error };
	*d++ = { "expected macro arguments for function-like macro", DiagnosticSeverity::Error };
	*d++ = { "expected net type specifier", DiagnosticSeverity::Error };
	*d++ = { "can't redefine compiler directive as a macro", DiagnosticSeverity::Error };
	*d++ = { "too many arguments provided to function-like macro", DiagnosticSeverity::Error };
	*d++ = { "not enough arguments provided to function-like macro", DiagnosticSeverity::Error };

	// parser
	*d++ = { "expected identifier", DiagnosticSeverity::Error };
	*d++ = { "expected '{}'", DiagnosticSeverity::Error };
	*d++ = { "expected data type (implicit type name not allowed)", DiagnosticSeverity::Error };
	*d++ = { "multiple types given in single declaration; this is not allowed in SystemVerilog", DiagnosticSeverity::Error };
	*d++ = { "misplaced colon; did you mean to use a dot?", DiagnosticSeverity::Error };
	*d++ = { "invalid token in member list", DiagnosticSeverity::Error };
	*d++ = { "invalid token in sequential block", DiagnosticSeverity::Error };
	*d++ = { "expected statement", DiagnosticSeverity::Error };
	*d++ = { "expected parameter declaration", DiagnosticSeverity::Error };
	*d++ = { "expected non-ansi port declaration", DiagnosticSeverity::Error };
	*d++ = { "expected ansi port declaration", DiagnosticSeverity::Error };
	*d++ = { "expected for loop initializer", DiagnosticSeverity::Error };
	*d++ = { "expected expression", DiagnosticSeverity::Error };
	*d++ = { "expected open range element", DiagnosticSeverity::Error };
	*d++ = { "expected stream expression", DiagnosticSeverity::Error };
	*d++ = { "expected argument", DiagnosticSeverity::Error };
	*d++ = { "expected variable declarator", DiagnosticSeverity::Error };
	*d++ = { "expected conditional pattern", DiagnosticSeverity::Error };
	*d++ = { "expected attribute", DiagnosticSeverity::Error };
	*d++ = { "expected package import", DiagnosticSeverity::Error };
	*d++ = { "expected hierarhical instantiation", DiagnosticSeverity::Error };
	*d++ = { "expected port connection", DiagnosticSeverity::Error };
	*d++ = { "expected vector literal digits", DiagnosticSeverity::Error };
	*d++ = { "expected variable assignment", DiagnosticSeverity::Error };
	*d++ = { "expected interface class name", DiagnosticSeverity::Error };
	*d++ = { "expected assignment key", DiagnosticSeverity::Error };
	*d++ = { "expected dist item", DiagnosticSeverity::Error };

	// declarations
	*d++ = { "ExpectedDistItem", DiagnosticSeverity::Error };
	*d++ = { "ExpectedDistItem", DiagnosticSeverity::Error };

	ASSERT((int)DiagCode::MaxValue == (d - &descriptors[0]), "When you add a new diagnostic code you need to update default messages");
}

void DiagnosticWriter::setMessage(DiagCode code, std::string format) {
	descriptors[(int)code].format = std::move(format);
}

void DiagnosticWriter::setSeverity(DiagCode code, DiagnosticSeverity severity) {
	descriptors[(int)code].severity = severity;
}

DiagnosticSeverity DiagnosticWriter::getSeverity(DiagCode code) const {
	return descriptors[(int)code].severity;
}

std::string DiagnosticWriter::report(const Diagnostic& diagnostic) {
	// walk out until we find a location for this diagnostic that isn't inside a macro
	Buffer<SourceLocation> expansionLocs;
	SourceLocation location = diagnostic.location;
	while (sourceManager.isMacroLoc(location)) {
		expansionLocs.append(location);
		location = sourceManager.getExpansionLoc(location);
	}

	// build the error message from arguments, if we have any
	Descriptor& desc = descriptors[(int)diagnostic.code];
	std::string msg;
	switch (diagnostic.args.size()) {
		case 0: msg = desc.format; break;
		case 1: msg = fmt::format(desc.format, diagnostic.args[0]); break;
		case 2: msg = fmt::format(desc.format, diagnostic.args[0], diagnostic.args[1]); break;
		default:
			ASSERT(false, "Too many arguments to diagnostic format. Add another switch case!");
	}

	fmt::MemoryWriter writer;
	formatDiag(writer, location, severityToString[(int)desc.severity], msg);

	// write out macro expansions, if we have any
	while (!expansionLocs.empty()) {
		location = expansionLocs.back();
		expansionLocs.pop();
		formatDiag(writer, sourceManager.getOriginalLoc(location), "note", "expanded from here");
	}

	return writer.str();
}

std::string DiagnosticWriter::report(Diagnostics& diagnostics) {
    // first sort diagnostics by file so that we can cut down
    // on the amount of include information we print out
    std::sort(diagnostics.begin(), diagnostics.end(), [this](auto& x, auto& y) { return sortDiagnostics(x, y); });

    std::deque<SourceLocation> includeStack;
    BufferID lastBuffer;
    fmt::MemoryWriter writer;

    for (auto& diag : diagnostics) {
        SourceLocation loc = getFullyExpandedLoc(diag.location);
        if (loc.buffer() != lastBuffer) {
            // We're looking at diagnostics from another file now. See if we should print
            // include stack info before we go on with the reports.
            lastBuffer = loc.buffer();
            getIncludeStack(lastBuffer, includeStack);

            for (auto& includeLoc : includeStack) {
                writer.write("In file included from {}:{}:\n",
                    sourceManager.getBufferName(includeLoc.buffer()),
                    sourceManager.getLineNumber(includeLoc)
                );
            }
        }
		writer << report(diag);
    }
    return writer.str();
}

SourceLocation DiagnosticWriter::getFullyExpandedLoc(SourceLocation loc) {
	while (sourceManager.isMacroLoc(loc))
		loc = sourceManager.getExpansionLoc(loc);
	return loc;
}

bool DiagnosticWriter::sortDiagnostics(const Diagnostic& x, const Diagnostic& y) {
	// start by expanding out macro locations
	SourceLocation xl = getFullyExpandedLoc(x.location);
	SourceLocation yl = getFullyExpandedLoc(y.location);
	return xl < yl;
}

StringRef DiagnosticWriter::getBufferLine(SourceLocation location, uint32_t col) {
	StringRef text = sourceManager.getSourceText(location.buffer());
	if (!text)
		return nullptr;

	const char* start = text.begin() + location.offset() - (col - 1);
	const char* curr = start;
	while (*curr != '\n' && *curr != '\r' && *curr != '\0')
		curr++;

	return StringRef(start, (uint32_t)(curr - start));
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

template<typename T>
void DiagnosticWriter::formatDiag(T& writer, SourceLocation loc, const char* severity, const std::string& msg) {
	uint32_t col = sourceManager.getColumnNumber(loc);
	writer.write("{}:{}:{}: {}: {}",
		sourceManager.getBufferName(loc.buffer()),
		sourceManager.getLineNumber(loc),
		col,
		severity,
		msg
	);

	StringRef line = getBufferLine(loc, col);
	if (line) {
		writer.write("\n{}\n", line);
		for (unsigned i = 0; i < col - 1; i++) {
			if (line[i] == '\t')
				writer << '\t';
			else
				writer << ' ';
		}
		writer << '^';
	}
	writer << '\n';
}

}