#include "Diagnostics.h"

#include "../external/cppformat/format.h"

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
    { "non-printable character in source text; SystemVerilog only supports ASCII text" },
    { "UTF-8 sequence in source text; SystemVerilog only supports ASCII text" },
    { "Unicode BOM at start of source text; SystemVerilog only supports ASCII text" },
    { "embedded NUL in source text; are you sure this is source code?" },
    { "expected directive name" },
    { "expected newline after escape sequence; remove trailing whitespace" },
    { "missing closing quote" },
    { "block comment unclosed at end of file" },
    { "nested block comments are disallowed by SystemVerilog" },
    { "block comments on the same line as a directive must also be terminated on that line" },
    { "expected integer base specifier after signed specifier" },
    { "expected fractional digits after decimal" },
    { "octal escape code is too large to be an ASCII character" },
    { "invalid hexadecimal number" },
    { "unknown character escape sequence" },
    { "expected an include file name" },
    { "expected exponent digits" },
    
    // preprocessor
    { "CouldNotOpenIncludeFile" },
    { "ExceededMaxIncludeDepth" },
    { "UnknownDirective" },
    { "expected end of directive (missing newline?)" },
    { "ExpectedEndOfMacroArgs" },
    { "ExpectedEndIfDirective" },
    { "UnexpectedDirective" },
    { "UnbalancedMacroArgDims" },
    { "ExpectedMacroArgs" },

    // parser
    { "SyntaxError" },
    { "expected identifier" },
    { "expected '{}'" },
    { "ImplicitNotAllowed" },
    { "MultipleTypesInDeclaration" },
    { "DirectionOnInterfacePort" },
    { "ColonShouldBeDot" },
    { "invalid token in member list" },
    { "invalid token in sequential block" },
    { "expected statement" },
    { "ExpectedParameterPort" },
    { "ExpectedNonAnsiPort" },
    { "ExpectedAnsiPort" },
    { "ExpectedForInitializer" },
    { "ExpectedExpression" },
    { "ExpectedInsideElement" },
    { "ExpectedStreamExpression" },
    { "ExpectedArgument" },
    { "ExpectedVariableDeclarator" },
    { "ExpectedConditionalPattern" },
    { "ExpectedAttribute" },
    { "ExpectedPackageImport" },
    { "ExpectedHierarchicalInstantiation" },
    { "ExpectedPortConnection" },
    { "ExpectedVectorDigits" },
    { "ExpectedVariableAssignment" },
    { "ExpectedInterfaceClassName" }
};

static StringRef getBufferLine(SourceManager& sourceManager, SourceLocation location, uint32_t col);

Diagnostics::Diagnostics() :
    Buffer::Buffer(128)
{
}

Diagnostic& Diagnostics::add(DiagCode code, SourceLocation location) {
    emplace(code, location);
    return last();
}

DiagnosticReport Diagnostics::getReport(const Diagnostic& diagnostic) const {
    auto& descriptor = diagnosticDescriptors[(int)diagnostic.code];
    return {
        diagnostic,
        descriptor.format,
        descriptor.severity
    };
}

Diagnostic::Arg::Arg(StringRef strRef) :
    strRef(strRef), type(STRINGREF)
{
}

Diagnostic::Diagnostic(DiagCode code, SourceLocation location) :
    code(code), location(location)
{
}

std::ostream& operator <<(std::ostream& os, const Diagnostic::Arg& arg) {
    switch (arg.type) {
        case Diagnostic::Arg::STRINGREF: os << arg.strRef; break;
        default:
            ASSERT(false && "Unknown arg type. Missing case!");
    }
    return os;
}

Diagnostic& operator <<(Diagnostic& diag, Diagnostic::Arg&& arg) {
    diag.args.push_back(std::move(arg));
    return diag;
}

DiagnosticReport::DiagnosticReport(const Diagnostic& diagnostic, StringRef format, DiagnosticSeverity severity) :
    diagnostic(diagnostic), format(format), severity(severity)
{
}

std::string DiagnosticReport::toString(SourceManager& sourceManager) const {
    auto location = diagnostic.location;
    uint32_t col = sourceManager.getColumnNumber(location);

    fmt::MemoryWriter writer;
    writer.write("{}:{}:{}: {}: ",
        sourceManager.getFileName(location.file),
        sourceManager.getLineNumber(location),
        col,
        severityToString[(int)severity]
    );

    // build the error message from arguments, if we have any
    switch (diagnostic.args.size()) {
        case 0: writer << format.toString(); break;
        case 1: writer.write(format.toString(), diagnostic.args[0]); break;
        case 2: writer.write(format.toString(), diagnostic.args[0], diagnostic.args[1]); break;
        default:
            ASSERT(false && "Too many arguments to diagnostic format. Add another switch case!");
    }

    // print out the source line, if possible
    StringRef line = getBufferLine(sourceManager, location, col);
    if (!line)
        writer << '\n';
    else {
        writer.write("\n{}\n", line);
        for (unsigned i = 0; i < col - 1; i++) {
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
    const char* curr = start;
    while (*curr != '\n' && *curr != '\r' && *curr != '\0')
        curr++;

    return StringRef(start, (uint32_t)(curr - start));
}

}