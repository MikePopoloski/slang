//------------------------------------------------------------------------------
// Token.cpp
// Contains Token class and related helpers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/parsing/Token.h"

#include "slang/diagnostics/ParserDiags.h"
#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/util/BumpAllocator.h"

namespace slang {

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
    const byte* extra() const { return reinterpret_cast<const byte*>(this + 1); }

    logic_t& bit() { return *reinterpret_cast<logic_t*>(extra()); }
    double& real() { return *reinterpret_cast<double*>(extra()); }
    SVIntStorage& integer() { return *reinterpret_cast<SVIntStorage*>(extra()); }
    string_view& stringText() { return *reinterpret_cast<string_view*>(extra()); }
    SyntaxKind& directiveKind() { return *reinterpret_cast<SyntaxKind*>(extra()); }

    const logic_t& bit() const { return *reinterpret_cast<const logic_t*>(extra()); }
    const double& real() const { return *reinterpret_cast<const double*>(extra()); }
    const SVIntStorage& integer() const { return *reinterpret_cast<const SVIntStorage*>(extra()); }
    const string_view& stringText() const { return *reinterpret_cast<const string_view*>(extra()); }
    const SyntaxKind& directiveKind() const {
        return *reinterpret_cast<const SyntaxKind*>(extra());
    }
};

static constexpr size_t getExtraSize(TokenKind kind) {
    size_t size = 0;
    switch (kind) {
        case TokenKind::StringLiteral:
            size = sizeof(string_view);
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

Trivia::Trivia() : rawText{ "", 0 }, kind(TriviaKind::Unknown) {
}

Trivia::Trivia(TriviaKind kind, string_view rawText) :
    rawText{ rawText.data(), (uint32_t)rawText.size() }, kind(kind) {
}

Trivia::Trivia(TriviaKind kind, span<Token const> tokens) :
    tokens{ tokens.data(), (uint32_t)tokens.size() }, kind(kind) {
}

Trivia::Trivia(TriviaKind kind, SyntaxNode* syntax) : syntaxNode(syntax), kind(kind) {
}

Trivia Trivia::withLocation(BumpAllocator& alloc, SourceLocation location) const {
    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedSyntax:
        case TriviaKind::SkippedTokens:
            return *this;
        default:
            break;
    }

    Trivia result;
    result.kind = kind;
    result.hasFullLocation = true;
    result.fullLocation = alloc.emplace<FullLocation>();
    result.fullLocation->text = getRawText();
    result.fullLocation->location = location;
    return result;
}

optional<SourceLocation> Trivia::getExplicitLocation() const {
    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedSyntax:
            return syntaxNode->getFirstToken().location();
        case TriviaKind::SkippedTokens:
            ASSERT(tokens.len);
            return tokens.ptr[0].location();
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

string_view Trivia::getRawText() const {
    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedSyntax:
        case TriviaKind::SkippedTokens:
            return "";
        default:
            if (hasFullLocation)
                return fullLocation->text;
            return { rawText.ptr, rawText.len };
    }
}

span<Token const> Trivia::getSkippedTokens() const {
    if (kind != TriviaKind::SkippedTokens)
        return {};
    return { tokens.ptr, tokens.len };
}

Token::Token() :
    kind(TokenKind::Unknown), missing(false), triviaCountSmall(0), reserved(0), numFlags() {
}

Token::Token(TokenKind kind, const Info* info, string_view rawText, size_t triviaCount) :
    kind(kind), missing(false),
    triviaCountSmall(triviaCount > MaxTriviaSmallCount ? MaxTriviaSmallCount + 1
                                                       : uint8_t(triviaCount)),
    reserved(0), numFlags(), rawLen(uint32_t(rawText.size())), info(info) {
    ASSERT(info);
}

string_view Token::valueText() const {
    switch (kind) {
        case TokenKind::StringLiteral:
            return info->stringText();
        case TokenKind::Identifier:
            switch (identifierType()) {
                case IdentifierType::Normal:
                case IdentifierType::System:
                    return rawText();
                case IdentifierType::Escaped:
                    // strip off leading backslash
                    return rawText().substr(1);
                case IdentifierType::Unknown:
                    // unknown tokens don't have value text
                    return "";
            }
            break;
        default:
            return rawText();
    }
    THROW_UNREACHABLE;
}

string_view Token::rawText() const {
    string_view text = getTokenKindText(kind);
    if (!text.empty())
        return text;

    // not a simple token, so extract info from our data pointer
    switch (kind) {
        case TokenKind::Unknown:
        case TokenKind::Identifier:
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
            return string_view(info->rawTextPtr, rawLen);
        case TokenKind::EndOfFile:
            return "";
        default:
            THROW_UNREACHABLE;
    }
}

SourceRange Token::range() const {
    return SourceRange(location(), location() + rawText().length());
}

SourceLocation Token::location() const {
    return info->location;
}

span<Trivia const> Token::trivia() const {
    if (triviaCountSmall == 0)
        return {};

    auto ptr = reinterpret_cast<const Trivia* const*>(info->extra() + getExtraSize(kind));
    if (triviaCountSmall == MaxTriviaSmallCount + 1)
        return { *ptr, ptrdiff_t(*reinterpret_cast<const size_t*>(ptr + 1)) };

    return { *ptr, triviaCountSmall };
}

std::string Token::toString() const {
    return SyntaxPrinter().print(*this).str();
}

SVInt Token::intValue() const {
    ASSERT(kind == TokenKind::IntegerLiteral);
    return info->integer();
}

double Token::realValue() const {
    ASSERT(kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);
    return info->real();
}

logic_t Token::bitValue() const {
    ASSERT(kind == TokenKind::UnbasedUnsizedLiteral);
    return info->bit();
}

NumericTokenFlags Token::numericFlags() const {
    ASSERT(kind == TokenKind::IntegerBase || kind == TokenKind::TimeLiteral ||
           kind == TokenKind::RealLiteral);
    return numFlags;
}

IdentifierType Token::identifierType() const {
    if (kind == TokenKind::Identifier)
        return idType;
    return IdentifierType::Unknown;
}

SyntaxKind Token::directiveKind() const {
    ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    return info->directiveKind();
}

Token Token::withTrivia(BumpAllocator& alloc, span<Trivia const> trivia) const {
    return clone(alloc, trivia, rawText(), location());
}

Token Token::withLocation(BumpAllocator& alloc, SourceLocation location) const {
    return clone(alloc, trivia(), rawText(), location);
}

Token Token::withRawText(BumpAllocator& alloc, string_view rawText) const {
    return clone(alloc, trivia(), rawText, location());
}

Token Token::clone(BumpAllocator& alloc, span<Trivia const> trivia, string_view rawText,
                   SourceLocation location) const {
    auto newInfo = createInfo(alloc, kind, trivia, rawText, location);
    memcpy(newInfo->extra(), info->extra(), getExtraSize(kind));

    Token result(kind, newInfo, rawText, trivia.size());
    result.missing = missing;
    result.info = newInfo;

    memcpy(&result.numFlags, &numFlags, 1);

    return result;
}

Token::Info* Token::createInfo(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                               string_view rawText, SourceLocation location) {
    size_t extra = getExtraSize(kind);
    ASSERT(extra % alignof(void*) == 0);

    size_t size = sizeof(Info) + extra;
    if (!trivia.empty()) {
        size += sizeof(Trivia*);
        if (trivia.size() > MaxTriviaSmallCount)
            size += sizeof(size_t);
    }

    auto info = (Info*)alloc.allocate(size, alignof(Info));
    info->location = location;
    info->rawTextPtr = rawText.data();

    if (!trivia.empty()) {
        const Trivia** triviaPtr = reinterpret_cast<const Trivia**>(info->extra() + extra);
        (*triviaPtr) = trivia.data();
        if (trivia.size() > MaxTriviaSmallCount)
            *reinterpret_cast<size_t*>(triviaPtr + 1) = trivia.size();
    }

    return info;
}

Token Token::create(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                    string_view rawText, SourceLocation location) {
    auto info = createInfo(alloc, kind, trivia, rawText, location);
    return Token(kind, info, rawText, trivia.size());
}

Token Token::create(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                    string_view rawText, SourceLocation location, string_view strText) {
    auto info = createInfo(alloc, kind, trivia, rawText, location);
    info->stringText() = strText;
    return Token(kind, info, rawText, trivia.size());
}

Token Token::create(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                    string_view rawText, SourceLocation location, IdentifierType idType) {
    auto info = createInfo(alloc, kind, trivia, rawText, location);

    Token result(kind, info, rawText, trivia.size());
    result.idType = idType;
    return result;
}

Token Token::create(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                    string_view rawText, SourceLocation location, SyntaxKind directive) {
    auto info = createInfo(alloc, kind, trivia, rawText, location);
    info->directiveKind() = directive;
    return Token(kind, info, rawText, trivia.size());
}

Token Token::create(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                    string_view rawText, SourceLocation location, logic_t bit) {
    auto info = createInfo(alloc, kind, trivia, rawText, location);
    info->bit() = bit;
    return Token(kind, info, rawText, trivia.size());
}

Token Token::create(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                    string_view rawText, SourceLocation location, const SVInt& value) {
    auto info = createInfo(alloc, kind, trivia, rawText, location);

    SVIntStorage storage(value.getBitWidth(), value.isSigned(), value.hasUnknown());
    if (value.isSingleWord())
        storage.val = *value.getRawPtr();
    else {
        storage.pVal =
            (uint64_t*)alloc.allocate(sizeof(uint64_t) * value.getNumWords(), alignof(uint64_t));
        memcpy(storage.pVal, value.getRawPtr(), sizeof(uint64_t) * value.getNumWords());
    }

    info->integer() = storage;
    return Token(kind, info, rawText, trivia.size());
}

Token Token::create(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                    string_view rawText, SourceLocation location, double value, bool outOfRange,
                    optional<TimeUnit> timeUnit) {
    auto info = createInfo(alloc, kind, trivia, rawText, location);
    info->real() = value;

    Token result(kind, info, rawText, trivia.size());
    result.numFlags.setOutOfRange(outOfRange);
    if (timeUnit)
        result.numFlags.set(*timeUnit);

    return result;
}

Token Token::create(BumpAllocator& alloc, TokenKind kind, span<Trivia const> trivia,
                    string_view rawText, SourceLocation location, LiteralBase base, bool isSigned) {
    auto info = createInfo(alloc, kind, trivia, rawText, location);

    Token result(kind, info, rawText, trivia.size());
    result.numFlags.set(base, isSigned);
    return result;
}

Token Token::createMissing(BumpAllocator& alloc, TokenKind kind, SourceLocation location) {
    Token result;
    switch (kind) {
        case TokenKind::Identifier:
            result = create(alloc, kind, {}, "", location, IdentifierType::Unknown);
            break;
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
            result = create(alloc, kind, {}, "", location, "");
            break;
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            result = create(alloc, kind, {}, "", location, SyntaxKind::Unknown);
            break;
        case TokenKind::IntegerLiteral:
            result = create(alloc, kind, {}, "", location, SVInt::Zero);
            break;
        case TokenKind::IntegerBase:
            result = create(alloc, kind, {}, "", location, LiteralBase::Decimal, false);
            break;
        case TokenKind::UnbasedUnsizedLiteral:
            result = create(alloc, kind, {}, "", location, logic_t::x);
            break;
        case TokenKind::RealLiteral:
            result = create(alloc, kind, {}, "", location, 0.0, false, std::nullopt);
            break;
        case TokenKind::TimeLiteral:
            result = create(alloc, kind, {}, "", location, 0.0, false, TimeUnit::Seconds);
            break;
        default:
            result = create(alloc, kind, {}, "", location);
            break;
    }

    result.missing = true;
    return result;
}

Token Token::createExpected(BumpAllocator& alloc, Diagnostics& diagnostics, Token actual,
                            TokenKind expected, Token lastConsumed) {
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
        if ((diag.location == location || diag.location == actual.location()) &&
            (diag.code == diag::ExpectedIdentifier || diag.code == diag::ExpectedToken)) {
            report = false;
        }
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
            default:
                diagnostics.add(diag::ExpectedToken, location) << getTokenKindText(expected);
                break;
        }
    }
    return Token::createMissing(alloc, expected, location);
}

} // namespace slang
