//------------------------------------------------------------------------------
// Token.cpp
// Contains Token class and related helpers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/Token.h"

#include "slang/diagnostics/ParserDiags.h"
#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/util/BumpAllocator.h"

namespace slang::parsing {

using namespace syntax;

// Heap-allocated info block. This structure is variably sized based on the
// actual type of token. Type-specific data is stored at the end, followed
// by any trivia if the token has it.
struct Token::Info {
    // Pointer to the raw text for the token; the size is stored in the token itself.
    const char* rawTextPtr;

    // The original location in the source text (or a macro location
    // if the token was generated during macro expansion).
    SourceLocation location;

    byte* extra() { return reinterpret_cast<byte*>(this + 1); }

    logic_t& bit() { return *reinterpret_cast<logic_t*>(extra()); }
    double& real() { return *reinterpret_cast<double*>(extra()); }
    SVIntStorage& integer() { return *reinterpret_cast<SVIntStorage*>(extra()); }
    std::string_view& stringText() { return *reinterpret_cast<std::string_view*>(extra()); }
    SyntaxKind& directiveKind() { return *reinterpret_cast<SyntaxKind*>(extra()); }
};

static constexpr size_t getExtraSize(TokenKind kind) {
    size_t size = 0;
    switch (kind) {
        case TokenKind::StringLiteral:
        case TokenKind::IncludeFileName:
            size = sizeof(std::string_view);
            break;
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
            size = sizeof(double);
            break;
        case TokenKind::IntegerLiteral:
            size = sizeof(SVIntStorage);
            break;
        case TokenKind::UnbasedUnsizedLiteral:
            size = sizeof(logic_t);
            break;
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            size = sizeof(SyntaxKind);
            break;
        default:
            return 0;
    }

    size_t align = alignof(void*);
    return (size + align - 1) & ~(align - 1);
}

void NumericTokenFlags::set(LiteralBase base_, bool isSigned_) {
    raw |= uint8_t(base_);
    raw |= uint8_t(isSigned_) << 2;
}

void NumericTokenFlags::set(TimeUnit unit_) {
    raw |= uint8_t(unit_) << 3;
}

void NumericTokenFlags::setOutOfRange(bool value) {
    raw |= uint8_t(value) << 6;
}

Trivia::Trivia() : rawText{"", 0}, kind(TriviaKind::Unknown) {
}

Trivia::Trivia(TriviaKind kind, std::string_view rawText) :
    rawText{rawText.data(), (uint32_t)rawText.size()}, kind(kind) {
}

Trivia::Trivia(TriviaKind kind, std::span<Token const> tokens) :
    tokens{tokens.data(), (uint32_t)tokens.size()}, kind(kind) {
}

Trivia::Trivia(TriviaKind kind, SyntaxNode* syntax) : syntaxNode(syntax), kind(kind) {
}

Trivia Trivia::withLocation(BumpAllocator& alloc, SourceLocation anchorLocation) const {
    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedSyntax:
        case TriviaKind::SkippedTokens:
            return *this;
        default:
            break;
    }

    auto resultLocation = alloc.emplace<FullLocation>();
    resultLocation->text = getRawText();
    resultLocation->location = anchorLocation - resultLocation->text.size();

    Trivia result;
    result.kind = kind;
    result.hasFullLocation = true;
    result.fullLocation = resultLocation;
    return result;
}

// Get the start location of a token including its trivia
static SourceLocation tokenLocationInclTrivia(const Token& token) {
    size_t locOffset = 0;

    // We iterate over trivia until we hit one which has explicit location.
    // All trivia without explicit location must be raw source text, for which
    // we can easily query its length and add it to the offset.
    for (const Trivia& trivia : token.trivia()) {
        if (auto loc = trivia.getExplicitLocation())
            return *loc - locOffset;
        else
            locOffset += trivia.getRawText().size();
    }

    return token.location() - locOffset;
}

std::optional<SourceLocation> Trivia::getExplicitLocation() const {
    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedSyntax:
            return tokenLocationInclTrivia(syntaxNode->getFirstToken());
        case TriviaKind::SkippedTokens:
            SLANG_ASSERT(tokens.len);
            return tokenLocationInclTrivia(tokens.ptr[0]);
        default:
            if (hasFullLocation)
                return fullLocation->location;

            return std::nullopt;
    }
}

SyntaxNode* Trivia::syntax() const {
    if (kind == TriviaKind::Directive || kind == TriviaKind::SkippedSyntax)
        return syntaxNode;
    return nullptr;
}

std::string_view Trivia::getRawText() const {
    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedSyntax:
        case TriviaKind::SkippedTokens:
            return "";
        default:
            if (hasFullLocation)
                return fullLocation->text;
            return {rawText.ptr, rawText.len};
    }
}

std::span<Token const> Trivia::getSkippedTokens() const {
    if (kind != TriviaKind::SkippedTokens)
        return {};
    return {tokens.ptr, tokens.len};
}

Trivia Trivia::clone(BumpAllocator& alloc, bool deep) const {
    Trivia result;
    result.kind = kind;
    result.hasFullLocation = hasFullLocation;

    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedSyntax:
            if (deep)
                result.syntaxNode = syntax::deepClone(*syntaxNode, alloc);
            else
                result.syntaxNode = syntaxNode;
            break;
        case TriviaKind::SkippedTokens:
            result.tokens = tokens;
            break;
        default:
            if (hasFullLocation) {
                result.fullLocation = alloc.emplace<FullLocation>();
                result.fullLocation->text = fullLocation->text;
                result.fullLocation->location = fullLocation->location;
            }
            else {
                result.rawText = rawText;
            }
            break;
    }

    return result;
}

Token::Token() :
    kind(TokenKind::Unknown), missing(false), triviaCountSmall(0), reserved(0), numFlags() {
}

Token::Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
             std::string_view rawText, SourceLocation location) {
    init(alloc, kind, trivia, rawText, location);
}

Token::Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
             std::string_view rawText, SourceLocation location, std::string_view strText) {
    SLANG_ASSERT(kind == TokenKind::StringLiteral || kind == TokenKind::IncludeFileName);
    init(alloc, kind, trivia, rawText, location);
    info->stringText() = strText;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
             std::string_view rawText, SourceLocation location, SyntaxKind directive) {
    SLANG_ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    init(alloc, kind, trivia, rawText, location);
    info->directiveKind() = directive;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
             std::string_view rawText, SourceLocation location, logic_t bit) {
    SLANG_ASSERT(kind == TokenKind::UnbasedUnsizedLiteral);
    init(alloc, kind, trivia, rawText, location);
    info->bit() = bit;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
             std::string_view rawText, SourceLocation location, const SVInt& value) {
    SLANG_ASSERT(kind == TokenKind::IntegerLiteral);
    init(alloc, kind, trivia, rawText, location);

    SVIntStorage storage(value.getBitWidth(), value.isSigned(), value.hasUnknown());
    if (value.isSingleWord())
        storage.val = *value.getRawPtr();
    else {
        storage.pVal = (uint64_t*)alloc.allocate(sizeof(uint64_t) * value.getNumWords(),
                                                 alignof(uint64_t));
        memcpy(storage.pVal, value.getRawPtr(), sizeof(uint64_t) * value.getNumWords());
    }

    info->integer() = storage;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
             std::string_view rawText, SourceLocation location, double value, bool outOfRange,
             std::optional<TimeUnit> timeUnit) {
    SLANG_ASSERT(kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);
    init(alloc, kind, trivia, rawText, location);
    info->real() = value;

    numFlags.setOutOfRange(outOfRange);
    if (timeUnit)
        numFlags.set(*timeUnit);
}

Token::Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
             std::string_view rawText, SourceLocation location, LiteralBase base, bool isSigned) {
    init(alloc, kind, trivia, rawText, location);
    numFlags.set(base, isSigned);
}

std::string_view Token::valueText() const {
    switch (kind) {
        case TokenKind::StringLiteral:
            return info->stringText();
        case TokenKind::Identifier: {
            std::string_view result = rawText();
            if (!result.empty() && result[0] == '\\')
                result = result.substr(1);
            return result;
        }
        default:
            return rawText();
    }
}

std::string_view Token::rawText() const {
    std::string_view text = LexerFacts::getTokenKindText(kind);
    if (!text.empty())
        return text;

    // not a simple token, so extract info from our data pointer
    switch (kind) {
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
        case TokenKind::IntegerLiteral:
        case TokenKind::IntegerBase:
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
        case TokenKind::EmptyMacroArgument:
        case TokenKind::LineContinuation:
            return std::string_view(info->rawTextPtr, rawLen);
        case TokenKind::Unknown:
            if (info)
                return std::string_view(info->rawTextPtr, rawLen);
            return "";
        case TokenKind::Placeholder:
        case TokenKind::EndOfFile:
            return "";
        default:
            SLANG_UNREACHABLE;
    }
}

SourceRange Token::range() const {
    return SourceRange(location(), location() + rawText().length());
}

SourceLocation Token::location() const {
    if (!info)
        return SourceLocation::NoLocation;
    return info->location;
}

std::span<Trivia const> Token::trivia() const {
    if (triviaCountSmall == 0)
        return {};

    const Trivia* trivia;
    byte* ptr = info->extra() + getExtraSize(kind);
    memcpy(reinterpret_cast<void*>(&trivia), ptr, sizeof(trivia));

    if (triviaCountSmall == MaxTriviaSmallCount + 1) {
        size_t size;
        memcpy(&size, ptr + sizeof(trivia), sizeof(size_t));
        return {trivia, size};
    }

    return {trivia, triviaCountSmall};
}

std::string Token::toString() const {
    return SyntaxPrinter().print(*this).str();
}

SVInt Token::intValue() const {
    SLANG_ASSERT(kind == TokenKind::IntegerLiteral);
    return info->integer();
}

double Token::realValue() const {
    SLANG_ASSERT(kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);
    return info->real();
}

logic_t Token::bitValue() const {
    SLANG_ASSERT(kind == TokenKind::UnbasedUnsizedLiteral);
    return info->bit();
}

NumericTokenFlags Token::numericFlags() const {
    SLANG_ASSERT(kind == TokenKind::IntegerBase || kind == TokenKind::TimeLiteral ||
                 kind == TokenKind::RealLiteral);
    return numFlags;
}

SyntaxKind Token::directiveKind() const {
    SLANG_ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    return info->directiveKind();
}

bool Token::isOnSameLine() const {
    for (auto& t : trivia()) {
        switch (t.kind) {
            case TriviaKind::LineComment:
            case TriviaKind::EndOfLine:
            case TriviaKind::SkippedSyntax:
            case TriviaKind::SkippedTokens:
            case TriviaKind::DisabledText:
                return false;
            case TriviaKind::Directive:
                if (t.syntax()->kind != SyntaxKind::MacroUsage)
                    return false;
                break;
            case TriviaKind::BlockComment:
                if (size_t offset = t.getRawText().find_first_of("\r\n");
                    offset != std::string_view::npos) {
                    return false;
                }
                break;
            default:
                break;
        }
    }
    return true;
}

Token Token::withTrivia(BumpAllocator& alloc, std::span<Trivia const> trivia) const {
    return clone(alloc, trivia, rawText(), location());
}

Token Token::withLocation(BumpAllocator& alloc, SourceLocation location) const {
    return clone(alloc, trivia(), rawText(), location);
}

Token Token::withRawText(BumpAllocator& alloc, std::string_view rawText) const {
    return clone(alloc, trivia(), rawText, location());
}

Token Token::clone(BumpAllocator& alloc, std::span<Trivia const> trivia, std::string_view rawText,
                   SourceLocation location) const {
    Token result(alloc, kind, trivia, rawText, location);
    result.missing = missing;

    memcpy(result.info->extra(), info->extra(), getExtraSize(kind));
    memcpy(&result.numFlags, &numFlags, 1);

    return result;
}

Token Token::deepClone(BumpAllocator& alloc) const {
    if (!info) {
        // No extra information, don't alloc extra info
        // If allocated it, the valid() function would fail
        return *this;
    }

    SmallVector<Trivia> triviaBuffer(trivia().size(), UninitializedTag());
    for (const auto& t : trivia())
        triviaBuffer.push_back(t.clone(alloc, true));
    return clone(alloc, triviaBuffer.copy(alloc), rawText(), location());
}

void Token::init(BumpAllocator& alloc, TokenKind kind_, std::span<Trivia const> trivia,
                 std::string_view rawText, SourceLocation location) {
    kind = kind_;
    missing = false;
    triviaCountSmall = 0;
    reserved = 0;
    numFlags.raw = 0;
    rawLen = uint32_t(rawText.size());

    size_t extra = getExtraSize(kind);
    SLANG_ASSERT(extra % alignof(void*) == 0);

    size_t size = sizeof(Info) + extra;
    if (!trivia.empty()) {
        size += sizeof(Trivia*);
        if (trivia.size() > MaxTriviaSmallCount) {
            size += sizeof(size_t);
            triviaCountSmall = MaxTriviaSmallCount + 1;
        }
        else {
            triviaCountSmall = uint8_t(trivia.size());
        }
    }

    info = (Info*)alloc.allocate(size, alignof(Info));
    info->location = location;
    info->rawTextPtr = rawText.data();

    if (!trivia.empty()) {
        const Trivia* triviaPtr = trivia.data();
        byte* dest = info->extra() + extra;
        memcpy(dest, reinterpret_cast<const void*>(&triviaPtr), sizeof(triviaPtr));

        if (trivia.size() > MaxTriviaSmallCount) {
            size = trivia.size();
            memcpy(dest + sizeof(triviaPtr), &size, sizeof(size_t));
        }
    }
}

Token Token::createMissing(BumpAllocator& alloc, TokenKind kind, SourceLocation location) {
    Token result;
    switch (kind) {
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
            result = Token(alloc, kind, {}, "", location, "");
            break;
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            result = Token(alloc, kind, {}, "", location, SyntaxKind::Unknown);
            break;
        case TokenKind::IntegerLiteral:
            result = Token(alloc, kind, {}, "", location, SVInt::Zero);
            break;
        case TokenKind::IntegerBase:
            result = Token(alloc, kind, {}, "", location, LiteralBase::Decimal, false);
            break;
        case TokenKind::UnbasedUnsizedLiteral:
            result = Token(alloc, kind, {}, "", location, logic_t::x);
            break;
        case TokenKind::RealLiteral:
            result = Token(alloc, kind, {}, "", location, 0.0, false, std::nullopt);
            break;
        case TokenKind::TimeLiteral:
            result = Token(alloc, kind, {}, "", location, 0.0, false, TimeUnit::Seconds);
            break;
        default:
            result = Token(alloc, kind, {}, "", location);
            break;
    }

    result.missing = true;
    return result;
}

Token Token::createExpected(BumpAllocator& alloc, Diagnostics& diagnostics, Token actual,
                            TokenKind expected, Token lastConsumed, Token matchingDelim) {
    // Figure out the best place to report this error based on the current
    // token as well as the last real token we consumed.
    SourceLocation location;
    if (!lastConsumed)
        location = actual.location();
    else {
        location = lastConsumed.location();
        location = location + lastConsumed.rawText().length();
    }

    // If there is already a diagnostic issued for this location, don't report this
    // one as well since it will just lead to lots of spam and the first error is
    // probably the thing that actually caused the issue.
    bool report = true;
    if (!diagnostics.empty()) {
        const Diagnostic& diag = diagnostics.back();
        if (diag.isError() && (diag.location == location || diag.location == actual.location()))
            report = false;
    }

    if (report) {
        switch (expected) {
            case TokenKind::Identifier:
                diagnostics.add(diag::ExpectedIdentifier, location);
                break;
            case TokenKind::StringLiteral:
                diagnostics.add(diag::ExpectedStringLiteral, location);
                break;
            case TokenKind::IntegerLiteral:
                diagnostics.add(diag::ExpectedIntegerLiteral, location);
                break;
            case TokenKind::TimeLiteral:
                diagnostics.add(diag::ExpectedTimeLiteral, location);
                break;
            case TokenKind::IncludeFileName:
                diagnostics.add(diag::ExpectedIncludeFileName, location);
                break;
            default: {
                auto& diag = diagnostics.add(diag::ExpectedToken, location);
                diag << LexerFacts::getTokenKindText(expected);
                if (matchingDelim) {
                    diag.addNote(diag::NoteToMatchThis, matchingDelim.location())
                        << LexerFacts::getTokenKindText(matchingDelim.kind);
                }
                break;
            }
        }
    }
    return Token::createMissing(alloc, expected, location);
}

} // namespace slang::parsing
