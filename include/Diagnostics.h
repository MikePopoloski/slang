#pragma once

#include "SourceLocation.h"

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
    ExpectedIntegerBaseAfterSigned,
    MissingFractionalDigits,
    OctalEscapeCodeTooBig,
    InvalidHexEscapeCode,
    UnknownEscapeCode,
    ExpectedIncludeFileName,
    RealExponentTooLarge,
    SignedLiteralTooLarge,
    MissingExponentDigits,

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
    ExpectedIdentifier,
    ExpectedToken,
    ImplicitNotAllowed,
    MultipleTypesInDeclaration,
    DirectionOnInterfacePort,
    ColonShouldBeDot,
    InvalidTokenInMemberList,
    InvalidTokenInSequentialBlock,
    ExpectedStatement,
    ExpectedParameterPort,
    ExpectedNonAnsiPort,
    ExpectedAnsiPort,
    ExpectedForInitializer,
    ExpectedExpression,
    ExpectedInsideElement,
    ExpectedStreamExpression,
    ExpectedArgument,
    ExpectedVariableDeclarator,
    ExpectedConditionalPattern,
    ExpectedAttribute,
    ExpectedPackageImport,
    ExpectedHierarchicalInstantiation,
    ExpectedPortConnection
};

std::ostream& operator<<(std::ostream& os, DiagCode code);

class Diagnostic {
public:
    struct Arg {
        StringRef strRef;
        uint8_t type;

        Arg(StringRef strRef) : strRef(strRef), type(STRINGREF) {}

        friend std::ostream& operator <<(std::ostream& os, const Arg& arg) {
            switch (arg.type) {
                case STRINGREF: os << arg.strRef; break;
                default:
                    ASSERT(false && "Unknown arg type. Missing case!");
            }
            return os;
        }

        enum {
            STRINGREF
        };
    };

    std::deque<Arg> args;
    DiagCode code;
    SourceLocation location;
    int width;

    Diagnostic(DiagCode code, SourceLocation location, int width) :
        code(code), location(location), width(width)
    {
    }

    friend Diagnostic& operator <<(Diagnostic& diag, Arg arg) {
        diag.args.push_back(std::move(arg));
        return diag;
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

    std::string toString(SourceManager& sourceManager) const;
};

class Diagnostics : public Buffer<Diagnostic> {
public:
    Diagnostics();

    Diagnostic& add(DiagCode code, SourceLocation location);
    DiagnosticReport getReport(const Diagnostic& diagnostic) const;
};

}