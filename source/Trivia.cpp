#include <cstdint>
#include <string>
#include <ostream>
#include <algorithm>

#include "BumpAllocator.h"
#include "StringRef.h"
#include "Buffer.h"
#include "Token.h"
#include "Trivia.h"

namespace slang {

void SimpleTrivia::writeTo(Buffer<char>& buffer) {
    buffer.appendRange(rawText);
}

void SimpleDirectiveTrivia::writeTo(Buffer<char>& buffer) {
    directive->writeTo(buffer, true);
}

void IncludeDirectiveTrivia::writeTo(Buffer<char>& buffer) {
    directive->writeTo(buffer, true);
}

void SkippedTokensTrivia::writeTo(Buffer<char>& buffer) {
    for (auto& token : tokens)
        token->writeTo(buffer, true);
}

std::ostream& operator<<(std::ostream& os, TriviaKind kind) {
    // auto-generated
    switch (kind) {
        case TriviaKind::Unknown: os << "Unknown"; break;
        case TriviaKind::Whitespace: os << "Whitespace"; break;
        case TriviaKind::EndOfLine: os << "EndOfLine"; break;
        case TriviaKind::LineContinuation: os << "LineContinuation"; break;
        case TriviaKind::LineComment: os << "LineComment"; break;
        case TriviaKind::BlockComment: os << "BlockComment"; break;
        case TriviaKind::DisabledText: os << "DisabledText"; break;
        case TriviaKind::SkippedTokens: os << "SkippedTokens"; break;
        case TriviaKind::MacroUsage: os << "MacroUsage"; break;
        case TriviaKind::BeginKeywordsDirective: os << "BeginKeywordsDirective"; break;
        case TriviaKind::CellDefineDirective: os << "CellDefineDirective"; break;
        case TriviaKind::DefaultNetTypeDirective: os << "DefaultNetTypeDirective"; break;
        case TriviaKind::DefineDirective: os << "DefineDirective"; break;
        case TriviaKind::ElseDirective: os << "ElseDirective"; break;
        case TriviaKind::ElseIfDirective: os << "ElseIfDirective"; break;
        case TriviaKind::EndKeywordsDirective: os << "EndKeywordsDirective"; break;
        case TriviaKind::EndCellDefineDirective: os << "EndCellDefineDirective"; break;
        case TriviaKind::EndIfDirective: os << "EndIfDirective"; break;
        case TriviaKind::IfDefDirective: os << "IfDefDirective"; break;
        case TriviaKind::IfNDefDirective: os << "IfNDefDirective"; break;
        case TriviaKind::IncludeDirective: os << "IncludeDirective"; break;
        case TriviaKind::LineDirective: os << "LineDirective"; break;
        case TriviaKind::NoUnconnectedDriveDirective: os << "NoUnconnectedDriveDirective"; break;
        case TriviaKind::PragmaDirective: os << "PragmaDirective"; break;
        case TriviaKind::ResetAllDirective: os << "ResetAllDirective"; break;
        case TriviaKind::TimescaleDirective: os << "TimescaleDirective"; break;
        case TriviaKind::UnconnectedDriveDirective: os << "UnconnectedDriveDirective"; break;
        case TriviaKind::UndefDirective: os << "UndefDirective"; break;
        case TriviaKind::UndefineAllDirective: os << "UndefineAllDirective"; break;
        default: os << "<unknown>"; break;
    }
    return os;
}

}