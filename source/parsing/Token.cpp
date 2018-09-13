//------------------------------------------------------------------------------
// Token.cpp
// Contains Token class and related helpers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/parsing/Token.h"

#include "slang/diagnostics/Diagnostics.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/util/BumpAllocator.h"

namespace slang {

void NumericTokenFlags::set(LiteralBase base_, bool isSigned_) {
    raw |= uint8_t(base_);
    raw |= uint8_t(isSigned_) << 2;
}

void NumericTokenFlags::set(TimeUnit unit_) {
    raw |= uint8_t(unit_) << 3;
}

Trivia::Trivia() :
    rawText{ "", 0 }, kind(TriviaKind::Unknown)
{
}

Trivia::Trivia(TriviaKind kind, string_view rawText) :
    rawText{ rawText.data(), (uint32_t)rawText.size() }, kind(kind)
{
}

Trivia::Trivia(TriviaKind kind, span<Token const> tokens) :
    tokens{ tokens.data(), (uint32_t)tokens.size() }, kind(kind)
{
}

Trivia::Trivia(TriviaKind kind, SyntaxNode* syntax) :
    syntaxNode(syntax), kind(kind)
{
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

Token::Info::Info(span<Trivia const> trivia, string_view rawText, SourceLocation location, bitmask<TokenFlags> flags) :
    trivia(trivia), rawText(rawText), location(location), flags(flags)
{
}

void Token::Info::setBit(logic_t value) {
    NumericLiteralInfo* target = std::get_if<NumericLiteralInfo>(&extra);
    if (target)
        target->value = value;
    else {
        NumericLiteralInfo numInfo;
        numInfo.value = value;
        extra = numInfo;
    }
}

void Token::Info::setReal(double value) {
    NumericLiteralInfo* target = std::get_if<NumericLiteralInfo>(&extra);
    if (target)
        target->value = value;
    else {
        NumericLiteralInfo numInfo;
        numInfo.value = value;
        extra = numInfo;
    }
}

void Token::Info::setInt(BumpAllocator& alloc, const SVInt& value) {
    SVIntStorage storage(value.getBitWidth(), value.isSigned(), value.hasUnknown());
    if (value.isSingleWord())
        storage.val = *value.getRawData();
    else {
        storage.pVal = (uint64_t*)alloc.allocate(sizeof(uint64_t) * value.getNumWords(), alignof(uint64_t));
        memcpy(storage.pVal, value.getRawData(), sizeof(uint64_t) * value.getNumWords());
    }

    NumericLiteralInfo* target = std::get_if<NumericLiteralInfo>(&extra);
    if (target)
        target->value = storage;
    else {
        NumericLiteralInfo numInfo;
        numInfo.value = storage;
        extra = numInfo;
    }
}

void Token::Info::setNumFlags(LiteralBase base, bool isSigned) {
    NumericLiteralInfo* target = std::get_if<NumericLiteralInfo>(&extra);
    if (target)
        target->numericFlags.set(base, isSigned);
    else {
        NumericLiteralInfo numInfo;
        numInfo.numericFlags.set(base, isSigned);
        extra = numInfo;
    }
}

void Token::Info::setTimeUnit(TimeUnit unit) {
    NumericLiteralInfo* target = std::get_if<NumericLiteralInfo>(&extra);
    if (target)
        target->numericFlags.set(unit);
    else {
        NumericLiteralInfo numInfo;
        numInfo.numericFlags.set(unit);
        extra = numInfo;
    }
}

Token::Token() :
    kind(TokenKind::Unknown), info(nullptr)
{
}

Token::Token(TokenKind kind, const Info* info) :
    kind(kind), info(info)
{
    ASSERT(info);
}

string_view Token::valueText() const {
    switch (kind) {
        case TokenKind::Identifier:
            switch (identifierType()) {
                case IdentifierType::Normal:
                case IdentifierType::System:
                    return info->rawText;
                case IdentifierType::Escaped:
                    // strip off leading backslash
                    return info->rawText.substr(1);
                case IdentifierType::Unknown:
                    // unknown tokens don't have value text
                    return "";
            }
            break;
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
            return info->stringText();
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            return info->rawText;
        default:
            return getTokenKindText(kind);
    }
    THROW_UNREACHABLE;
}

string_view Token::rawText() const {
    string_view text = getTokenKindText(kind);
    if (!text.empty())
        return text;
    else {
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
                return info->rawText;
            case TokenKind::EndOfDirective:
            case TokenKind::EndOfFile:
                return "";
            default: THROW_UNREACHABLE;
        }
    }
}

SourceRange Token::range() const {
    return SourceRange(location(), location() + rawText().length());
}

std::string Token::toString() const {
    return SyntaxPrinter().print(*this).str();
}

SVInt Token::intValue() const {
    ASSERT(kind == TokenKind::IntegerLiteral);
    return std::get<SVIntStorage>(info->numInfo().value);
}

double Token::realValue() const {
    ASSERT(kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);
    return std::get<double>(info->numInfo().value);
}

logic_t Token::bitValue() const {
    ASSERT(kind == TokenKind::UnbasedUnsizedLiteral);
    return std::get<logic_t>(info->numInfo().value);
}

NumericTokenFlags Token::numericFlags() const {
    ASSERT(kind == TokenKind::IntegerBase || kind == TokenKind::TimeLiteral);
    return info->numInfo().numericFlags;
}

IdentifierType Token::identifierType() const {
    if (kind == TokenKind::Identifier)
        return info->idType();
    return IdentifierType::Unknown;
}

SyntaxKind Token::directiveKind() const {
    ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    return info->directiveKind();
}

bool Token::hasTrivia(TriviaKind triviaKind) const {
    for (const auto& t : info->trivia) {
        if (t.kind == triviaKind)
            return true;
    }
    return false;
}

Token Token::withTrivia(BumpAllocator& alloc, span<Trivia const> trivia) const {
    auto newInfo = alloc.emplace<Info>(*info);
    newInfo->trivia = trivia;
    return Token(kind, newInfo);
}

Token Token::withLocation(BumpAllocator& alloc, SourceLocation location) const {
    auto newInfo = alloc.emplace<Info>(*info);
    newInfo->location = location;
    return Token(kind, newInfo);
}

Token Token::createMissing(BumpAllocator& alloc, TokenKind kind, SourceLocation location) {
    auto info = alloc.emplace<Info>();
    info->location = location;
    info->flags = TokenFlags::Missing;

    switch (kind) {
        case TokenKind::Identifier:
            info->extra = IdentifierType::Unknown;
            break;
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
            info->extra = string_view("");
            break;
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            info->extra = SyntaxKind::Unknown;
            break;
        case TokenKind::IntegerLiteral:
            info->setInt(alloc, 0);
            break;
        case TokenKind::IntegerBase:
            info->setNumFlags(LiteralBase::Decimal, false);
            break;
        case TokenKind::UnbasedUnsizedLiteral:
            info->setBit(logic_t::x);
            break;
        case TokenKind::RealLiteral:
            info->setReal(0.0);
            break;
        case TokenKind::TimeLiteral:
            info->setTimeUnit(TimeUnit::Seconds);
            break;
        default:
            break;
    }

    return Token(kind, info);
}

Token Token::createExpected(BumpAllocator& alloc, Diagnostics& diagnostics, Token actual, TokenKind expected, Token lastConsumed) {
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
            (diag.code == DiagCode::ExpectedIdentifier ||
             diag.code == DiagCode::ExpectedToken)) {
            report = false;
        }
    }

    if (report) {
        switch (expected) {
            case TokenKind::Identifier:
                diagnostics.add(DiagCode::ExpectedIdentifier, location);
                break;
            case TokenKind::StringLiteral:
                diagnostics.add(DiagCode::ExpectedStringLiteral, location);
                break;
            case TokenKind::IntegerLiteral:
                diagnostics.add(DiagCode::ExpectedIntegerLiteral, location);
                break;
            case TokenKind::TimeLiteral:
                diagnostics.add(DiagCode::ExpectedTimeLiteral, location);
                break;
            default:
                diagnostics.add(DiagCode::ExpectedToken, location) << getTokenKindText(expected);
                break;
        }
    }
    return Token::createMissing(alloc, expected, location);
}

}
