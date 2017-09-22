//------------------------------------------------------------------------------
// Token.cpp
// Contains Token class and related helpers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Token.h"

#include "diagnostics/Diagnostics.h"
#include "util/BumpAllocator.h"

namespace slang {

void NumericTokenFlags::set(LiteralBase base_, bool isSigned_) {
    raw |= uint8_t(base_);
    raw |= uint8_t(isSigned_) << 2;
}

void NumericTokenFlags::set(TimeUnit unit_) {
    raw |= uint8_t(unit_) << 3;
}

Token::Info::Info() :
    flags(0)
{
}

Token::Info::Info(span<Trivia const> trivia, string_view rawText, SourceLocation location, int flags) :
    trivia(trivia), rawText(rawText), location(location), flags((uint8_t)flags)
{
}

void Token::Info::setNumInfo(NumericTokenValue&& value) {
    NumericLiteralInfo* target = std::get_if<NumericLiteralInfo>(&extra);
    if (target)
        target->value = std::move(value);
    else {
        NumericLiteralInfo numInfo;
        numInfo.value = std::move(value);
        extra = std::move(numInfo);
    }
}

void Token::Info::setNumFlags(LiteralBase base, bool isSigned) {
    NumericLiteralInfo* target = std::get_if<NumericLiteralInfo>(&extra);
    if (target)
        target->numericFlags.set(base, isSigned);
    else {
        NumericLiteralInfo numInfo;
        numInfo.numericFlags.set(base, isSigned);
        extra = std::move(numInfo);
    }
}

void Token::Info::setTimeUnit(TimeUnit unit) {
    NumericLiteralInfo* target = std::get_if<NumericLiteralInfo>(&extra);
    if (target)
        target->numericFlags.set(unit);
    else {
        NumericLiteralInfo numInfo;
        numInfo.numericFlags.set(unit);
        extra = std::move(numInfo);
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
        case TokenKind::SystemIdentifier:
            return info->rawText;
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
                return info->rawText;
            case TokenKind::EndOfDirective:
            case TokenKind::EndOfFile:
                return "";
            default: THROW_UNREACHABLE;
        }
    }
}

void Token::writeTo(SmallVector<char>& buffer, uint8_t writeFlags) const {
    if (!(writeFlags & SyntaxToStringFlags::IncludePreprocessed) && isFromPreprocessor())
        return;

    if (writeFlags & SyntaxToStringFlags::IncludeTrivia) {
        for (const auto& t : info->trivia)
            t.writeTo(buffer, writeFlags);
    }

    if (!(writeFlags & SyntaxToStringFlags::IncludeMissing) && isMissing())
        return;

    buffer.appendRange(rawText());
}

std::string Token::toString(uint8_t writeFlags) const {
    SmallVectorSized<char, 256> buffer;
    writeTo(buffer, writeFlags);
    return std::string(buffer.begin(), buffer.end());
}

const NumericTokenValue& Token::numericValue() const {
    ASSERT(kind == TokenKind::IntegerLiteral || kind == TokenKind::UnbasedUnsizedLiteral ||
           kind == TokenKind::RealLiteral || kind == TokenKind::TimeLiteral);
    return info->numInfo().value;
}

NumericTokenFlags Token::numericFlags() const {
    ASSERT(kind == TokenKind::IntegerBase || kind == TokenKind::TimeLiteral);
    return info->numInfo().numericFlags;
}

IdentifierType Token::identifierType() const {
    if (kind == TokenKind::Identifier || kind == TokenKind::SystemIdentifier)
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

Token Token::asPreprocessed(BumpAllocator& alloc) const {
    auto newInfo = alloc.emplace<Info>(*info);
    newInfo->flags |= TokenFlags::IsFromPreprocessor;
    return Token(kind, newInfo);
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

    return Token(kind, info);
}

// for certain kinds of expected tokens we back up and report
// the error at the end of the previous token
static bool reportErrorAdjacent(TokenKind kind) {
    switch (kind) {
        case TokenKind::OpenBracket:
        case TokenKind::OpenParenthesis:
        case TokenKind::OpenParenthesisStar:
        case TokenKind::OpenParenthesisStarCloseParenthesis:
        case TokenKind::Semicolon:
        case TokenKind::Colon:
        case TokenKind::DoubleColon:
        case TokenKind::Comma:
        case TokenKind::Dot:
            return true;
        default:
            return false;
    }
}

Token Token::createExpected(BumpAllocator& alloc, Diagnostics& diagnostics, Token actual, TokenKind expected, Token lastConsumed) {
    // Figure out the best place to report this error based on the current
    // token as well as the last real token we consumed.
    SourceLocation location;
    if (!lastConsumed || !reportErrorAdjacent(expected))
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
        if (diag.location == location &&
            (diag.code == DiagCode::ExpectedIdentifier ||
             diag.code == DiagCode::ExpectedToken)) {
            report = false;
        }
    }

    if (report) {
        // Since identifiers are so common, give a specialized error here.
        if (expected == TokenKind::Identifier)
            diagnostics.add(DiagCode::ExpectedIdentifier, location);
        else
            diagnostics.add(DiagCode::ExpectedToken, location) << getTokenKindText(expected);
    }
    return Token::createMissing(alloc, expected, location);
}

}
