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
// by any trivia if the token has it, and then a raw text pointer if needed.
struct Token::Info {
    // The original location in the source text (or a macro location
    // if the token was generated during macro expansion).
    SourceLocation location;

    byte* extra() { return reinterpret_cast<byte*>(this + 1); }

    double& real() { return *reinterpret_cast<double*>(extra()); }
    SVIntStorage& integer() { return *reinterpret_cast<SVIntStorage*>(extra()); }
    std::string_view& stringText() { return *reinterpret_cast<std::string_view*>(extra()); }
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
        default:
            return 0;
    }

    size_t align = alignof(void*);
    return (size + align - 1) & ~(align - 1);
}

static bool needsRawText(TokenKind kind) {
    switch (kind) {
        case TokenKind::Unknown:
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
            return true;
        default:
            return false;
    }
}

// Inline-trivia codes (stored in the token's `triviaCountSmall` field when
// `hasInlineTrivia` is set). The 5-bit code space is partitioned as:
//   0..15  -> single Whitespace trivia of 1..16 ASCII spaces
//   16     -> single EndOfLine "\n"
//   17     -> single EndOfLine "\r\n"
//   18     -> pair: two EndOfLine "\n" trivia
//   19..31 -> pair: EndOfLine "\n" followed by Whitespace of 1..13 spaces
//             (the dominant "newline + indent" pattern)
constexpr uint8_t InlineMaxSpaceCount = 16;
constexpr uint8_t InlineCodeNewlineLF = 16;
constexpr uint8_t InlineCodeNewlineCRLF = 17;
constexpr uint8_t InlineCodeDoubleLF = 18;
constexpr uint8_t InlineCodeNewlineSpacesBase = 19;
constexpr uint8_t InlineMaxNewlineSpacesCount = 32 - InlineCodeNewlineSpacesBase;

// Static raw text used for synthesized inline whitespace trivia. Trivia objects
// returned from `Token::decodeInlineTrivia` reference substrings of this buffer.
constexpr std::string_view InlineSpacesText = "                "sv; // 16 spaces
constexpr std::string_view InlineLF = "\n"sv;
constexpr std::string_view InlineCRLF = "\r\n"sv;

// Returns 0 if `t` is not a Whitespace trivia of N>=1 plain ASCII spaces (with
// N <= maxCount). Otherwise returns N.
static uint8_t plainSpaceRunLength(const Trivia& t, uint8_t maxCount) {
    if (t.kind != TriviaKind::Whitespace)
        return 0;

    auto raw = t.getRawText();
    if (raw.empty() || raw.size() > maxCount)
        return 0;

    for (char c : raw) {
        if (c != ' ')
            return 0;
    }

    return uint8_t(raw.size());
}

static std::optional<uint8_t> encodeInlineTrivia(const Trivia& t) {
    // Only the simple trivia variants (those with a `rawText` payload and no
    // explicit location) can be inlined. Skip anything carrying a syntax node,
    // skipped tokens, or a non-default location.
    if (t.getExplicitLocation())
        return std::nullopt;

    auto raw = t.getRawText();
    switch (t.kind) {
        case TriviaKind::Whitespace: {
            uint8_t n = plainSpaceRunLength(t, InlineMaxSpaceCount);
            if (n == 0)
                return std::nullopt;
            return uint8_t(n - 1);
        }
        case TriviaKind::EndOfLine:
            if (raw == InlineLF)
                return InlineCodeNewlineLF;
            if (raw == InlineCRLF)
                return InlineCodeNewlineCRLF;
            return std::nullopt;
        default:
            return std::nullopt;
    }
}

static std::optional<uint8_t> encodeInlineTriviaPair(const Trivia& t0, const Trivia& t1) {
    // Supported inline pairs all start with a plain "\n".
    if (t0.kind != TriviaKind::EndOfLine || t0.getExplicitLocation() || t1.getExplicitLocation() ||
        t0.getRawText() != InlineLF) {
        return std::nullopt;
    }

    // Pair of two "\n" (blank line).
    if (t1.kind == TriviaKind::EndOfLine && t1.getRawText() == InlineLF)
        return InlineCodeDoubleLF;

    // "\n" followed by 1..N plain ASCII spaces.
    uint8_t n = plainSpaceRunLength(t1, InlineMaxNewlineSpacesCount);
    if (n == 0)
        return std::nullopt;

    return uint8_t(InlineCodeNewlineSpacesBase + n - 1);
}

static uint8_t decodeInlineTrivia(uint8_t code, Trivia* out) {
    if (code < InlineMaxSpaceCount) {
        out[0] = Trivia(TriviaKind::Whitespace, InlineSpacesText.substr(0, code + 1));
        return 1;
    }

    switch (code) {
        case InlineCodeNewlineLF:
            out[0] = Trivia(TriviaKind::EndOfLine, InlineLF);
            return 1;
        case InlineCodeNewlineCRLF:
            out[0] = Trivia(TriviaKind::EndOfLine, InlineCRLF);
            return 1;
        case InlineCodeDoubleLF:
            out[0] = Trivia(TriviaKind::EndOfLine, InlineLF);
            out[1] = Trivia(TriviaKind::EndOfLine, InlineLF);
            return 2;
        default: {
            SLANG_ASSERT(code >= InlineCodeNewlineSpacesBase);
            uint8_t spaces = uint8_t(code - InlineCodeNewlineSpacesBase + 1);
            SLANG_ASSERT(spaces <= InlineMaxNewlineSpacesCount);
            out[0] = Trivia(TriviaKind::EndOfLine, InlineLF);
            out[1] = Trivia(TriviaKind::Whitespace, InlineSpacesText.substr(0, spaces));
            return 2;
        }
    }
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
    kind(TokenKind::Unknown), missing(false), hasInfoPtr(false), hasInlineTrivia(false),
    triviaCountSmall(0), numFlags(), nonInfoLoc(SourceLocation::NoLocation) {
}

Token::Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
             std::string_view rawText, SourceLocation location) {
    init(alloc, kind, trivia, rawText, location);
}

Token::Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
             std::string_view rawText, SourceLocation location, std::string_view strText) {
    SLANG_ASSERT(kind == TokenKind::StringLiteral || kind == TokenKind::IncludeFileName);
    init(alloc, kind, trivia, rawText, location);
    getInfo().stringText() = strText;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
             std::string_view rawText, SourceLocation location, SyntaxKind directive) {
    SLANG_ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    init(alloc, kind, trivia, rawText, location);

    SLANG_ASSERT(rawText.length() < UINT16_MAX);
    uint32_t val = 0;
    memcpy(&val, &directive, sizeof(directive));
    SLANG_ASSERT(val < (1u << 15));
    rawLenAndExtra |= val << 16;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
             std::string_view rawText, SourceLocation location, KnownSystemName systemName) {
    SLANG_ASSERT(kind == TokenKind::SystemIdentifier);
    init(alloc, kind, trivia, rawText, location);

    SLANG_ASSERT(rawText.length() < UINT16_MAX);
    uint32_t val = 0;
    memcpy(&val, &systemName, sizeof(systemName));
    SLANG_ASSERT(val < (1u << 15));
    rawLenAndExtra |= val << 16;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
             std::string_view rawText, SourceLocation location, logic_t bit) {
    SLANG_ASSERT(kind == TokenKind::UnbasedUnsizedLiteral);
    init(alloc, kind, trivia, rawText, location);

    SLANG_ASSERT(rawText.length() < UINT16_MAX);
    uint32_t val = 0;
    memcpy(&val, &bit, sizeof(bit));
    rawLenAndExtra |= val << 16;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
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

    getInfo().integer() = storage;
}

Token::Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
             std::string_view rawText, SourceLocation location, double value, bool outOfRange,
             std::optional<TimeUnit> timeUnit) {
    SLANG_ASSERT(kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);
    init(alloc, kind, trivia, rawText, location);
    getInfo().real() = value;

    numFlags.setOutOfRange(outOfRange);
    if (timeUnit)
        numFlags.set(*timeUnit);
}

Token::Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
             std::string_view rawText, SourceLocation location, LiteralBase base, bool isSigned) {
    init(alloc, kind, trivia, rawText, location);
    numFlags.set(base, isSigned);
}

std::string_view Token::valueText() const {
    switch (kind) {
        case TokenKind::StringLiteral:
            return getInfo().stringText();
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

    auto getRaw = [this](uint32_t length) {
        byte* ptr = getInfo().extra() + getExtraSize(kind);
        const char* raw;
        memcpy(reinterpret_cast<void*>(&raw), ptr, sizeof(raw));
        return std::string_view(raw, length);
    };

    // not a simple token, so extract info from our data pointer
    switch (kind) {
        case TokenKind::Identifier:
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
        case TokenKind::IntegerLiteral:
        case TokenKind::IntegerBase:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
        case TokenKind::EmptyMacroArgument:
        case TokenKind::LineContinuation:
            return getRaw(rawLenAndExtra & ~TokenTag);
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
        case TokenKind::SystemIdentifier:
            return getRaw(rawLenAndExtra & 0xffff);
        case TokenKind::Unknown:
            if (hasInfoPtr && info)
                return getRaw(rawLenAndExtra & ~TokenTag);
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
    return hasInfoPtr ? getInfo().location : nonInfoLoc;
}

TriviaView Token::trivia() const {
    if (hasInlineTrivia) {
        std::array<Trivia, 2> buf;
        uint8_t n = decodeInlineTrivia(triviaCountSmall, buf.data());
        return TriviaView::makeInline(buf.data(), n);
    }

    if (triviaCountSmall == 0)
        return {};

    byte* ptr = getInfo().extra() + getExtraSize(kind);
    if (needsRawText(kind))
        ptr += sizeof(const char*);

    size_t count;
    if (triviaCountSmall == MaxTriviaSmallCount + 1) {
        memcpy(&count, ptr, sizeof(size_t));
        ptr += sizeof(size_t);
    }
    else {
        count = triviaCountSmall;
    }

    return std::span<Trivia const>{reinterpret_cast<const Trivia*>(ptr), count};
}

std::string Token::toString() const {
    return SyntaxPrinter().print(*this).str();
}

SVInt Token::intValue() const {
    SLANG_ASSERT(kind == TokenKind::IntegerLiteral);
    return getInfo().integer();
}

double Token::realValue() const {
    SLANG_ASSERT(kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);
    return getInfo().real();
}

logic_t Token::bitValue() const {
    SLANG_ASSERT(kind == TokenKind::UnbasedUnsizedLiteral);
    logic_t result;
    uint32_t val = rawLenAndExtra >> 16;
    memcpy(reinterpret_cast<byte*>(&result), &val, sizeof(result));
    return result;
}

NumericTokenFlags Token::numericFlags() const {
    SLANG_ASSERT(kind == TokenKind::IntegerBase || kind == TokenKind::TimeLiteral ||
                 kind == TokenKind::RealLiteral);
    return numFlags;
}

SyntaxKind Token::directiveKind() const {
    SLANG_ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    SyntaxKind result;
    uint32_t val = (rawLenAndExtra >> 16) & 0x7fff;
    memcpy(reinterpret_cast<byte*>(&result), &val, sizeof(result));
    return result;
}

KnownSystemName Token::systemName() const {
    SLANG_ASSERT(kind == TokenKind::SystemIdentifier);
    KnownSystemName result;
    uint32_t val = (rawLenAndExtra >> 16) & 0x7fff;
    memcpy(reinterpret_cast<byte*>(&result), &val, sizeof(result));
    return result;
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
    return kind != TokenKind::EndOfFile;
}

size_t Token::getSizeInBytes() const {
    size_t result = sizeof(Token);
    if (hasInfoPtr) {
        result += sizeof(Info) + getExtraSize(kind);
        if (needsRawText(kind))
            result += sizeof(const char*);

        result += getTriviaSizeInBytes();
    }
    return result;
}

size_t Token::getTriviaSizeInBytes() const {
    // Trivia stored inline in the token's bits doesn't contribute any
    // info-block bytes.
    if (hasInlineTrivia || triviaCountSmall == 0)
        return 0;

    size_t count = triviaCountSmall;
    size_t result = 0;
    if (triviaCountSmall > MaxTriviaSmallCount) {
        result += sizeof(size_t);
        count = trivia().size();
    }
    result += count * sizeof(Trivia);
    return result;
}

Token Token::withTrivia(BumpAllocator& alloc, const TriviaView& trivia) const {
    return clone(alloc, trivia, rawText(), location());
}

Token Token::withLocation(BumpAllocator& alloc, SourceLocation location) const {
    return clone(alloc, trivia(), rawText(), location);
}

Token Token::withRawText(BumpAllocator& alloc, std::string_view rawText) const {
    return clone(alloc, trivia(), rawText, location());
}

Token Token::clone(BumpAllocator& alloc, const TriviaView& trivia, std::string_view rawText,
                   SourceLocation location) const {
    Token result(alloc, kind, trivia, rawText, location);
    result.missing = missing;
    memcpy(&result.numFlags, &numFlags, 1);

    if (hasInfoPtr && result.hasInfoPtr)
        memcpy(result.getInfo().extra(), getInfo().extra(), getExtraSize(kind));

    switch (kind) {
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
        case TokenKind::SystemIdentifier:
            SLANG_ASSERT(rawText.length() < UINT16_MAX);
            result.rawLenAndExtra = (rawLenAndExtra & 0x7fff0000) | result.rawLenAndExtra;
            break;
        default:
            break;
    }

    return result;
}

Token Token::deepClone(BumpAllocator& alloc) const {
    if (!hasInfoPtr) {
        // No extra information, don't alloc extra info
        return *this;
    }

    SmallVector<Trivia> triviaBuffer(trivia().size(), UninitializedTag());
    for (const auto& t : trivia())
        triviaBuffer.push_back(t.clone(alloc, true));
    return clone(alloc, triviaBuffer, rawText(), location());
}

void Token::init(BumpAllocator& alloc, TokenKind kind_, const TriviaView& trivia,
                 std::string_view rawText, SourceLocation location) {
    kind = kind_;
    missing = false;
    hasInlineTrivia = false;
    triviaCountSmall = 0;
    numFlags.raw = 0;

    // If the trivia run is one or two simple elements that we can pack into
    // our free bits, do so and skip allocating any storage for them in the
    // info block. The two-element form covers the very common
    // "newline + indent" case.
    if (trivia.size() == 2) {
        if (auto code = encodeInlineTriviaPair(trivia[0], trivia[1])) {
            hasInlineTrivia = true;
            triviaCountSmall = *code;
        }
    }
    else if (trivia.size() == 1) {
        if (auto code = encodeInlineTrivia(trivia[0])) {
            hasInlineTrivia = true;
            triviaCountSmall = *code;
        }
    }

    size_t extra = getExtraSize(kind);
    SLANG_ASSERT(extra % alignof(void*) == 0);

    size_t size = sizeof(Info) + extra;
    const bool needsRaw = needsRawText(kind);
    if (needsRaw)
        size += sizeof(const char*);

    const bool storeTrivia = !hasInlineTrivia && !trivia.empty();
    if (storeTrivia) {
        if (trivia.size() > MaxTriviaSmallCount) {
            size += sizeof(size_t);
            triviaCountSmall = MaxTriviaSmallCount + 1;
        }
        else {
            triviaCountSmall = uint8_t(trivia.size());
        }
        size += trivia.size() * sizeof(Trivia);
    }

    if (!extra && !needsRaw && !storeTrivia) {
        hasInfoPtr = false;
        nonInfoLoc = location;
        return;
    }

    info = (Info*)alloc.allocate(size, alignof(Info));
    info->location = location;
    hasInfoPtr = true;

    byte* dest = info->extra() + extra;
    if (needsRaw) {
        rawLenAndExtra = uint32_t(rawText.size()) | TokenTag;

        auto dataPtr = rawText.data();
        memcpy(dest, reinterpret_cast<const void*>(&dataPtr), sizeof(dataPtr));
        dest += sizeof(dataPtr);
    }

    if (storeTrivia) {
        if (trivia.size() > MaxTriviaSmallCount) {
            size_t cnt = trivia.size();
            memcpy(dest, &cnt, sizeof(size_t));
            dest += sizeof(size_t);
        }
        memcpy(dest, trivia.data(), trivia.size() * sizeof(Trivia));
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
        case TokenKind::SystemIdentifier:
            result = Token(alloc, kind, {}, "", location, KnownSystemName::Unknown);
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
