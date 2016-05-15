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
    { "ExpectedVectorDigits" }
};

static StringRef getBufferLine(SourceManager& sourceManager, SourceLocation location, uint32_t col);

Diagnostics::Diagnostics() :
    Buffer::Buffer(128)
{
}

Diagnostic& Diagnostics::add(DiagCode code, SourceLocation location) {
    emplace(code, location, 0);
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
        CASE(ExpectedIntegerBaseAfterSigned);
        CASE(MissingFractionalDigits);
        CASE(OctalEscapeCodeTooBig);
        CASE(InvalidHexEscapeCode);
        CASE(UnknownEscapeCode);
        CASE(ExpectedIncludeFileName);
        CASE(MissingExponentDigits);
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
        CASE(ExpectedIdentifier);
        CASE(ExpectedToken);
        CASE(ImplicitNotAllowed);
        CASE(MultipleTypesInDeclaration);
        CASE(DirectionOnInterfacePort);
        CASE(ColonShouldBeDot);
        CASE(InvalidTokenInMemberList);
        CASE(InvalidTokenInSequentialBlock);
        CASE(ExpectedStatement);
        CASE(ExpectedParameterPort);
        CASE(ExpectedNonAnsiPort);
        CASE(ExpectedAnsiPort);
        CASE(ExpectedForInitializer);
        CASE(ExpectedExpression);
        CASE(ExpectedInsideElement);
        CASE(ExpectedStreamExpression);
        CASE(ExpectedArgument);
        CASE(ExpectedVariableDeclarator);
        CASE(ExpectedConditionalPattern);
        CASE(ExpectedAttribute);
        CASE(ExpectedPackageImport);
        CASE(ExpectedHierarchicalInstantiation);
        CASE(ExpectedPortConnection);
        CASE(ExpectedVectorDigits);
        default: ASSERT(false && "Missing case");
    }
    return os;
#undef CASE
}

}