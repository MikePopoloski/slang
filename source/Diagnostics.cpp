#include "Diagnostics.h"

#include "../external/fmt/format.h"
#include "../external/fmt/ostream.h"

#include "SourceManager.h"

namespace {

using namespace slang;

SourceLocation getFullyExpandedLoc(SourceManager& sourceManager, SourceLocation loc) {
    while (sourceManager.isMacroLoc(loc))
        loc = sourceManager.getExpansionLoc(loc);
    return loc;
}

bool sortDiagnostics(SourceManager& sourceManager, const Diagnostic& x, const Diagnostic& y) {
    // start by expanding out macro locations
    SourceLocation xl = getFullyExpandedLoc(sourceManager, x.location);
    SourceLocation yl = getFullyExpandedLoc(sourceManager, y.location);
    return xl < yl;
}

StringRef getBufferLine(SourceManager& sourceManager, SourceLocation location, uint32_t col) {
    const Buffer<char>* buffer = sourceManager.getBufferMemory(location.buffer);
    if (!buffer)
        return nullptr;

    const char* start = buffer->begin() + location.offset - (col - 1);
    const char* curr = start;
    while (*curr != '\n' && *curr != '\r' && *curr != '\0')
        curr++;

    return StringRef(start, (uint32_t)(curr - start));
}

void getIncludeStack(SourceManager& sourceManager, BufferID buffer, std::deque<SourceLocation>& stack) {
    stack.clear();
    while (buffer) {
        SourceLocation loc = sourceManager.getIncludedFrom(buffer);
        if (!loc.buffer)
            break;

        stack.push_front(loc);
        buffer = loc.buffer;
    }
}

void formatDiag(fmt::MemoryWriter& writer, SourceManager& sourceManager, SourceLocation loc,
    const char* severity, const std::string& msg) {

    uint32_t col = sourceManager.getColumnNumber(loc);
    writer.write("{}:{}:{}: {}: {}",
        sourceManager.getBufferName(loc.buffer),
        sourceManager.getLineNumber(loc),
        col,
        severity,
        msg
    );

    StringRef line = getBufferLine(sourceManager, loc, col);
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
    { "unexpected whitespace after escape character" },
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
    { "could not find or open include file" },
    { "ExceededMaxIncludeDepth" },
    { "unknown macro or compiler directive" },
    { "expected end of directive (missing newline?)" },
    { "ExpectedEndOfMacroArgs" },
    { "ExpectedEndIfDirective" },
    { "unexpected conditional directive" },
    { "UnbalancedMacroArgDims" },
    { "ExpectedMacroArgs" },
    { "expected net type specifier" },
    { "can't redefine compiler directive as a macro" },
    { "too many arguments provided to function-like macro" },
    { "not enough arguments provided to function-like macro" },

    // parser
    { "SyntaxError" },
    { "expected identifier" },
    { "expected '{}'" },
    { "expected data type (implicit type name not allowed)" },
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
    { "ExpectedInterfaceClassName" },
    { "ExpectedAssignmentKey" }
};

DiagnosticReport::DiagnosticReport(const Diagnostic& diagnostic, StringRef format, DiagnosticSeverity severity) :
    diagnostic(diagnostic), format(format), severity(severity)
{
}

std::string DiagnosticReport::toString(SourceManager& sourceManager) const {
    Buffer<SourceLocation> expansionLocs;
    SourceLocation location = diagnostic.location;
    while (sourceManager.isMacroLoc(location)) {
        expansionLocs.append(location);
        location = sourceManager.getExpansionLoc(location);
    }

    // build the error message from arguments, if we have any
    std::string msg;
    switch (diagnostic.args.size()) {
        case 0: msg = format.toString(); break;
        case 1: msg = fmt::format(format.toString(), diagnostic.args[0]); break;
        case 2: msg = fmt::format(format.toString(), diagnostic.args[0], diagnostic.args[1]); break;
        default:
            ASSERT(false, "Too many arguments to diagnostic format. Add another switch case!");
    }

    fmt::MemoryWriter writer;
    formatDiag(writer, sourceManager, location, severityToString[(int)severity], msg);

    // write out macro expansions, if we have any
    while (!expansionLocs.empty()) {
        location = expansionLocs.back();
        expansionLocs.pop();
        formatDiag(writer, sourceManager, sourceManager.getOriginalLoc(location), "note", "expanded from here");
    }

    return writer.str();
}

DiagnosticReport Diagnostic::toReport() const {
    auto& descriptor = diagnosticDescriptors[(int)code];
    return{
        *this,
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

Diagnostics::Diagnostics() :
    Buffer::Buffer(128)
{
}

Diagnostic& Diagnostics::add(DiagCode code, SourceLocation location) {
    emplace(code, location);
    return back();
}

std::string Diagnostics::reportAll(SourceManager& sourceManager) {
    // first sort diagnostics by file so that we can cut down
    // on the amount of include information we print out
    std::sort(begin(), end(), [&sourceManager](auto& x, auto& y) { return sortDiagnostics(sourceManager, x, y); });

    std::deque<SourceLocation> includeStack;
    BufferID lastBuffer;
    fmt::MemoryWriter writer;

    for (auto& diag : *this) {
        SourceLocation loc = getFullyExpandedLoc(sourceManager, diag.location);
        if (loc.buffer != lastBuffer) {
            // We're looking at diagnostics from another file now. See if we should print
            // include stack info before we go on with the reports.
            lastBuffer = loc.buffer;
            getIncludeStack(sourceManager, lastBuffer, includeStack);

            for (auto& loc : includeStack) {
                writer.write("In file included from {}:{}:\n",
                    sourceManager.getBufferName(loc.buffer),
                    sourceManager.getLineNumber(loc)
                );
            }
        }
        writer << diag.toReport().toString(sourceManager);
    }
    return writer.str();
}

}