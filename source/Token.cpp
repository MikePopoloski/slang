#include <cstdint>
#include <string>
#include <algorithm>

#include "BumpAllocator.h"
#include "StringRef.h"
#include "Token.h"
#include "StringTable.h"
#include "SyntaxFacts.h"

namespace slang {

Token::Token(TokenKind kind, ArrayRef<Trivia*> trivia) :
    kind(kind), trivia(trivia) {
}

void Token::writeTo(Buffer<char>& buffer, bool includeTrivia) const {
    if (includeTrivia) {
        for (const auto& t : trivia)
            t->writeTo(buffer);
    }

    StringRef text = getTokenKindText(kind);
    if (text)
        buffer.appendRange(text);
    else {
        // not a simple token, so extract info from our data pointer
        switch (kind) {
            case TokenKind::Unknown:
            case TokenKind::Identifier:
            case TokenKind::SystemIdentifier:
                buffer.appendRange(((IdentifierInfo*)(this + 1))->rawText);
                break;
            case TokenKind::IncludeFileName:
            case TokenKind::StringLiteral:
                buffer.appendRange(((StringLiteralInfo*)(this + 1))->rawText);
                break;
            case TokenKind::IntegerLiteral:
            case TokenKind::RealLiteral:
                buffer.appendRange(((NumericLiteralInfo*)(this + 1))->rawText);
                break;
            case TokenKind::Directive:
            case TokenKind::MacroUsage:
                buffer.appendRange(((DirectiveInfo*)(this + 1))->rawText);
                break;
        }
    }
}

StringRef Token::valueText() const {
    StringRef text = getTokenKindText(kind);
    if (text)
        return text;

    switch (kind) {
        case TokenKind::Identifier:
            switch (identifierType()) {
                case IdentifierType::Escaped:
                    // strip off leading backslash
                    return ((IdentifierInfo*)(this + 1))->rawText.subString(1);
                case IdentifierType::Unknown:
                    // unknown tokens don't have value text
                    return nullptr;
                default:
                    return ((IdentifierInfo*)(this + 1))->rawText;
            }
            break;
        case TokenKind::SystemIdentifier:
            return ((IdentifierInfo*)(this + 1))->rawText;
        case TokenKind::IncludeFileName:
        case TokenKind::StringLiteral:
            return ((StringLiteralInfo*)(this + 1))->niceText;
        case TokenKind::Directive:
        case TokenKind::MacroUsage:
            return ((DirectiveInfo*)(this + 1))->rawText;
        default:
            return nullptr;
    }
}

std::string Token::toString() const {
    Buffer<char> buffer;
    writeTo(buffer, false);
    return std::string(buffer.begin(), buffer.end());
}

std::string Token::toFullString() const {
    Buffer<char> buffer;
    writeTo(buffer, true);
    return std::string(buffer.begin(), buffer.end());
}

const NumericValue& Token::numericValue() const {
    ASSERT(kind == TokenKind::IntegerLiteral || kind == TokenKind::RealLiteral);
    return ((NumericLiteralInfo*)(this + 1))->value;
}

IdentifierType Token::identifierType() const {
    if (kind == TokenKind::Identifier || kind == TokenKind::SystemIdentifier)
        return ((IdentifierInfo*)(this + 1))->type;
    return IdentifierType::Unknown;
}

TriviaKind Token::directiveKind() const {
    ASSERT(kind == TokenKind::Directive || kind == TokenKind::MacroUsage);
    return ((DirectiveInfo*)(this + 1))->kind;
}

Token* Token::createUnknown(BumpAllocator& alloc, ArrayRef<Trivia*> trivia, StringRef rawText) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(IdentifierInfo));
    new (token) Token(TokenKind::Unknown, trivia);

    IdentifierInfo* info = (IdentifierInfo*)(token + 1);
    info->rawText = rawText;
    info->type = IdentifierType::Unknown;

    return token;
}

Token* Token::createSimple(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia*> trivia) {
    Token* token = (Token*)alloc.allocate(sizeof(Token));
    new (token) Token(kind, trivia);
    return token;
}

Token* Token::createIdentifier(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia*> trivia, StringRef rawText, IdentifierType type) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(IdentifierInfo));
    new (token) Token(kind, trivia);

    IdentifierInfo* info = (IdentifierInfo*)(token + 1);
    info->rawText = rawText;
    info->type = type;

    return token;
}

Token* Token::createStringLiteral(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia*> trivia, StringRef rawText, StringRef niceText) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(StringLiteralInfo));
    new (token) Token(kind, trivia);

    StringLiteralInfo* info = (StringLiteralInfo*)(token + 1);
    info->rawText = rawText;
    info->niceText = niceText;

    return token;
}

Token* Token::createNumericLiteral(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia*> trivia, StringRef rawText, NumericValue value) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(NumericLiteralInfo));
    new (token) Token(kind, trivia);

    NumericLiteralInfo* info = (NumericLiteralInfo*)(token + 1);
    info->rawText = rawText;
    info->value = value;

    return token;
}

Token* Token::createDirective(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia*> trivia, StringRef rawText, TriviaKind directiveKind) {
    Token* token = (Token*)alloc.allocate(sizeof(Token) + sizeof(DirectiveInfo));
    new (token) Token(kind, trivia);

    DirectiveInfo* info = (DirectiveInfo*)(token + 1);
    info->rawText = rawText;
    info->kind = directiveKind;

    return token;
}

Token* Token::missing(BumpAllocator& alloc, TokenKind kind, ArrayRef<Trivia*> trivia) {
    // TODO: flag missing
    switch (kind) {
        case TokenKind::Unknown:
            return createUnknown(alloc, trivia, nullptr);
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
            return createIdentifier(alloc, kind, trivia, nullptr, IdentifierType::Unknown);
        case TokenKind::IntegerLiteral:
        case TokenKind::RealLiteral:
            return createNumericLiteral(alloc, kind, trivia, nullptr, 0);
        case TokenKind::StringLiteral:
            return createStringLiteral(alloc, kind, trivia, nullptr, nullptr);
        case TokenKind::Directive:
            return createDirective(alloc, kind, trivia, nullptr, TriviaKind::Unknown);
        default:
            return createSimple(alloc, kind, trivia);
    }
}

std::ostream& operator<<(std::ostream& os, TokenKind kind) {
    // auto-generated
    switch (kind) {
        case TokenKind::Unknown: os << "Unknown"; break;
        case TokenKind::EndOfFile: os << "EndOfFile"; break;
        case TokenKind::Identifier: os << "Identifier"; break;
        case TokenKind::SystemIdentifier: os << "SystemIdentifier"; break;
        case TokenKind::StringLiteral: os << "StringLiteral"; break;
        case TokenKind::IntegerLiteral: os << "IntegerLiteral"; break;
        case TokenKind::RealLiteral: os << "RealLiteral"; break;
        case TokenKind::TimeLiteral: os << "TimeLiteral"; break;
        case TokenKind::ApostropheOpenBrace: os << "ApostropheOpenBrace"; break;
        case TokenKind::OpenBrace: os << "OpenBrace"; break;
        case TokenKind::CloseBrace: os << "CloseBrace"; break;
        case TokenKind::OpenBracket: os << "OpenBracket"; break;
        case TokenKind::CloseBracket: os << "CloseBracket"; break;
        case TokenKind::OpenParenthesis: os << "OpenParenthesis"; break;
        case TokenKind::OpenParenthesisStar: os << "OpenParenthesisStar"; break;
        case TokenKind::CloseParenthesis: os << "CloseParenthesis"; break;
        case TokenKind::StarCloseParenthesis: os << "StarCloseParenthesis"; break;
        case TokenKind::Semicolon: os << "Semicolon"; break;
        case TokenKind::Colon: os << "Colon"; break;
        case TokenKind::ColonEquals: os << "ColonEquals"; break;
        case TokenKind::ColonSlash: os << "ColonSlash"; break;
        case TokenKind::DoubleColon: os << "DoubleColon"; break;
        case TokenKind::StarDoubleColonStar: os << "StarDoubleColonStar"; break;
        case TokenKind::Comma: os << "Comma"; break;
        case TokenKind::DotStar: os << "DotStar"; break;
        case TokenKind::Dot: os << "Dot"; break;
        case TokenKind::Slash: os << "Slash"; break;
        case TokenKind::Star: os << "Star"; break;
        case TokenKind::DoubleStar: os << "DoubleStar"; break;
        case TokenKind::StarArrow: os << "StarArrow"; break;
        case TokenKind::Plus: os << "Plus"; break;
        case TokenKind::DoublePlus: os << "DoublePlus"; break;
        case TokenKind::PlusColon: os << "PlusColon"; break;
        case TokenKind::Minus: os << "Minus"; break;
        case TokenKind::DoubleMinus: os << "DoubleMinus"; break;
        case TokenKind::MinusColon: os << "MinusColon"; break;
        case TokenKind::MinusArrow: os << "MinusArrow"; break;
        case TokenKind::MinusDoubleArrow: os << "MinusDoubleArrow"; break;
        case TokenKind::Tilde: os << "Tilde"; break;
        case TokenKind::TildeAnd: os << "TildeAnd"; break;
        case TokenKind::TildeOr: os << "TildeOr"; break;
        case TokenKind::TildeXor: os << "TildeXor"; break;
        case TokenKind::Dollar: os << "Dollar"; break;
        case TokenKind::Question: os << "Question"; break;
        case TokenKind::Hash: os << "Hash"; break;
        case TokenKind::DoubleHash: os << "DoubleHash"; break;
        case TokenKind::HashMinusHash: os << "HashMinusHash"; break;
        case TokenKind::HashEqualsHash: os << "HashEqualsHash"; break;
        case TokenKind::Xor: os << "Xor"; break;
        case TokenKind::XorTilde: os << "XorTilde"; break;
        case TokenKind::Equals: os << "Equals"; break;
        case TokenKind::DoubleEquals: os << "DoubleEquals"; break;
        case TokenKind::DoubleEqualsQuestion: os << "DoubleEqualsQuestion"; break;
        case TokenKind::TripleEquals: os << "TripleEquals"; break;
        case TokenKind::EqualsArrow: os << "EqualsArrow"; break;
        case TokenKind::PlusEqual: os << "PlusEqual"; break;
        case TokenKind::MinusEqual: os << "MinusEqual"; break;
        case TokenKind::SlashEqual: os << "SlashEqual"; break;
        case TokenKind::StarEqual: os << "StarEqual"; break;
        case TokenKind::AndEqual: os << "AndEqual"; break;
        case TokenKind::OrEqual: os << "OrEqual"; break;
        case TokenKind::PercentEqual: os << "PercentEqual"; break;
        case TokenKind::XorEqual: os << "XorEqual"; break;
        case TokenKind::LeftShiftEqual: os << "LeftShiftEqual"; break;
        case TokenKind::TripleLeftShiftEqual: os << "TripleLeftShiftEqual"; break;
        case TokenKind::RightShiftEqual: os << "RightShiftEqual"; break;
        case TokenKind::TripleRightShiftEqual: os << "TripleRightShiftEqual"; break;
        case TokenKind::LeftShift: os << "LeftShift"; break;
        case TokenKind::RightShift: os << "RightShift"; break;
        case TokenKind::TripleLeftShift: os << "TripleLeftShift"; break;
        case TokenKind::TripleRightShift: os << "TripleRightShift"; break;
        case TokenKind::Exclamation: os << "Exclamation"; break;
        case TokenKind::ExclamationEquals: os << "ExclamationEquals"; break;
        case TokenKind::ExclamationEqualsQuestion: os << "ExclamationEqualsQuestion"; break;
        case TokenKind::ExclamationDoubleEquals: os << "ExclamationDoubleEquals"; break;
        case TokenKind::Percent: os << "Percent"; break;
        case TokenKind::LessThan: os << "LessThan"; break;
        case TokenKind::LessThanEquals: os << "LessThanEquals"; break;
        case TokenKind::LessThanMinusArrow: os << "LessThanMinusArrow"; break;
        case TokenKind::GreaterThan: os << "GreaterThan"; break;
        case TokenKind::GreaterThanEquals: os << "GreaterThanEquals"; break;
        case TokenKind::Or: os << "Or"; break;
        case TokenKind::DoubleOr: os << "DoubleOr"; break;
        case TokenKind::OrMinusArrow: os << "OrMinusArrow"; break;
        case TokenKind::OrEqualsArrow: os << "OrEqualsArrow"; break;
        case TokenKind::At: os << "At"; break;
        case TokenKind::DoubleAt: os << "DoubleAt"; break;
        case TokenKind::And: os << "And"; break;
        case TokenKind::DoubleAnd: os << "DoubleAnd"; break;
        case TokenKind::TripleAnd: os << "TripleAnd"; break;
        case TokenKind::AcceptOnKeyword: os << "AcceptOnKeyword"; break;
        case TokenKind::AliasKeyword: os << "AliasKeyword"; break;
        case TokenKind::AlwaysKeyword: os << "AlwaysKeyword"; break;
        case TokenKind::AlwaysCombKeyword: os << "AlwaysCombKeyword"; break;
        case TokenKind::AlwaysFFKeyword: os << "AlwaysFFKeyword"; break;
        case TokenKind::AlwaysLatchKeyword: os << "AlwaysLatchKeyword"; break;
        case TokenKind::AndKeyword: os << "AndKeyword"; break;
        case TokenKind::AssertKeyword: os << "AssertKeyword"; break;
        case TokenKind::AssignKeyword: os << "AssignKeyword"; break;
        case TokenKind::AssumeKeyword: os << "AssumeKeyword"; break;
        case TokenKind::AutomaticKeyword: os << "AutomaticKeyword"; break;
        case TokenKind::BeforeKeyword: os << "BeforeKeyword"; break;
        case TokenKind::BeginKeyword: os << "BeginKeyword"; break;
        case TokenKind::BindKeyword: os << "BindKeyword"; break;
        case TokenKind::BinsKeyword: os << "BinsKeyword"; break;
        case TokenKind::BinsOfKeyword: os << "BinsOfKeyword"; break;
        case TokenKind::BitKeyword: os << "BitKeyword"; break;
        case TokenKind::BreakKeyword: os << "BreakKeyword"; break;
        case TokenKind::BufKeyword: os << "BufKeyword"; break;
        case TokenKind::BufIf0Keyword: os << "BufIf0Keyword"; break;
        case TokenKind::BufIf1Keyword: os << "BufIf1Keyword"; break;
        case TokenKind::ByteKeyword: os << "ByteKeyword"; break;
        case TokenKind::CaseKeyword: os << "CaseKeyword"; break;
        case TokenKind::CaseXKeyword: os << "CaseXKeyword"; break;
        case TokenKind::CaseZKeyword: os << "CaseZKeyword"; break;
        case TokenKind::CellKeyword: os << "CellKeyword"; break;
        case TokenKind::CHandleKeyword: os << "CHandleKeyword"; break;
        case TokenKind::CheckerKeyword: os << "CheckerKeyword"; break;
        case TokenKind::ClassKeyword: os << "ClassKeyword"; break;
        case TokenKind::ClockingKeyword: os << "ClockingKeyword"; break;
        case TokenKind::CmosKeyword: os << "CmosKeyword"; break;
        case TokenKind::ConfigKeyword: os << "ConfigKeyword"; break;
        case TokenKind::ConstKeyword: os << "ConstKeyword"; break;
        case TokenKind::ConstraintKeyword: os << "ConstraintKeyword"; break;
        case TokenKind::ContextKeyword: os << "ContextKeyword"; break;
        case TokenKind::ContinueKeyword: os << "ContinueKeyword"; break;
        case TokenKind::CoverKeyword: os << "CoverKeyword"; break;
        case TokenKind::CoverGroupKeyword: os << "CoverGroupKeyword"; break;
        case TokenKind::CoverPointKeyword: os << "CoverPointKeyword"; break;
        case TokenKind::CrossKeyword: os << "CrossKeyword"; break;
        case TokenKind::DeassignKeyword: os << "DeassignKeyword"; break;
        case TokenKind::DefaultKeyword: os << "DefaultKeyword"; break;
        case TokenKind::DefParamKeyword: os << "DefParamKeyword"; break;
        case TokenKind::DesignKeyword: os << "DesignKeyword"; break;
        case TokenKind::DisableKeyword: os << "DisableKeyword"; break;
        case TokenKind::DistKeyword: os << "DistKeyword"; break;
        case TokenKind::DoKeyword: os << "DoKeyword"; break;
        case TokenKind::EdgeKeyword: os << "EdgeKeyword"; break;
        case TokenKind::ElseKeyword: os << "ElseKeyword"; break;
        case TokenKind::EndKeyword: os << "EndKeyword"; break;
        case TokenKind::EndCaseKeyword: os << "EndCaseKeyword"; break;
        case TokenKind::EndCheckerKeyword: os << "EndCheckerKeyword"; break;
        case TokenKind::EndClassKeyword: os << "EndClassKeyword"; break;
        case TokenKind::EndClockingKeyword: os << "EndClockingKeyword"; break;
        case TokenKind::EndConfigKeyword: os << "EndConfigKeyword"; break;
        case TokenKind::EndFunctionKeyword: os << "EndFunctionKeyword"; break;
        case TokenKind::EndGenerateKeyword: os << "EndGenerateKeyword"; break;
        case TokenKind::EndGroupKeyword: os << "EndGroupKeyword"; break;
        case TokenKind::EndInterfaceKeyword: os << "EndInterfaceKeyword"; break;
        case TokenKind::EndModuleKeyword: os << "EndModuleKeyword"; break;
        case TokenKind::EndPackageKeyword: os << "EndPackageKeyword"; break;
        case TokenKind::EndPrimitiveKeyword: os << "EndPrimitiveKeyword"; break;
        case TokenKind::EndProgramKeyword: os << "EndProgramKeyword"; break;
        case TokenKind::EndPropertyKeyword: os << "EndPropertyKeyword"; break;
        case TokenKind::EndSpecifyKeyword: os << "EndSpecifyKeyword"; break;
        case TokenKind::EndSequenceKeyword: os << "EndSequenceKeyword"; break;
        case TokenKind::EndTableKeyword: os << "EndTableKeyword"; break;
        case TokenKind::EndTaskKeyword: os << "EndTaskKeyword"; break;
        case TokenKind::EnumKeyword: os << "EnumKeyword"; break;
        case TokenKind::EventKeyword: os << "EventKeyword"; break;
        case TokenKind::EventuallyKeyword: os << "EventuallyKeyword"; break;
        case TokenKind::ExpectKeyword: os << "ExpectKeyword"; break;
        case TokenKind::ExportKeyword: os << "ExportKeyword"; break;
        case TokenKind::ExtendsKeyword: os << "ExtendsKeyword"; break;
        case TokenKind::ExternKeyword: os << "ExternKeyword"; break;
        case TokenKind::FinalKeyword: os << "FinalKeyword"; break;
        case TokenKind::FirstMatchKeyword: os << "FirstMatchKeyword"; break;
        case TokenKind::ForKeyword: os << "ForKeyword"; break;
        case TokenKind::ForceKeyword: os << "ForceKeyword"; break;
        case TokenKind::ForeachKeyword: os << "ForeachKeyword"; break;
        case TokenKind::ForeverKeyword: os << "ForeverKeyword"; break;
        case TokenKind::ForkKeyword: os << "ForkKeyword"; break;
        case TokenKind::ForkJoinKeyword: os << "ForkJoinKeyword"; break;
        case TokenKind::FunctionKeyword: os << "FunctionKeyword"; break;
        case TokenKind::GenerateKeyword: os << "GenerateKeyword"; break;
        case TokenKind::GenVarKeyword: os << "GenVarKeyword"; break;
        case TokenKind::GlobalKeyword: os << "GlobalKeyword"; break;
        case TokenKind::HighZ0Keyword: os << "HighZ0Keyword"; break;
        case TokenKind::HighZ1Keyword: os << "HighZ1Keyword"; break;
        case TokenKind::IfKeyword: os << "IfKeyword"; break;
        case TokenKind::IffKeyword: os << "IffKeyword"; break;
        case TokenKind::IfNoneKeyword: os << "IfNoneKeyword"; break;
        case TokenKind::IgnoreBinsKeyword: os << "IgnoreBinsKeyword"; break;
        case TokenKind::IllegalBinsKeyword: os << "IllegalBinsKeyword"; break;
        case TokenKind::ImplementsKeyword: os << "ImplementsKeyword"; break;
        case TokenKind::ImpliesKeyword: os << "ImpliesKeyword"; break;
        case TokenKind::ImportKeyword: os << "ImportKeyword"; break;
        case TokenKind::IncDirKeyword: os << "IncDirKeyword"; break;
        case TokenKind::IncludeKeyword: os << "IncludeKeyword"; break;
        case TokenKind::InitialKeyword: os << "InitialKeyword"; break;
        case TokenKind::InOutKeyword: os << "InOutKeyword"; break;
        case TokenKind::InputKeyword: os << "InputKeyword"; break;
        case TokenKind::InsideKeyword: os << "InsideKeyword"; break;
        case TokenKind::InstanceKeyword: os << "InstanceKeyword"; break;
        case TokenKind::IntKeyword: os << "IntKeyword"; break;
        case TokenKind::IntegerKeyword: os << "IntegerKeyword"; break;
        case TokenKind::InterconnectKeyword: os << "InterconnectKeyword"; break;
        case TokenKind::InterfaceKeyword: os << "InterfaceKeyword"; break;
        case TokenKind::IntersectKeyword: os << "IntersectKeyword"; break;
        case TokenKind::JoinKeyword: os << "JoinKeyword"; break;
        case TokenKind::JoinAnyKeyword: os << "JoinAnyKeyword"; break;
        case TokenKind::JoinNoneKeyword: os << "JoinNoneKeyword"; break;
        case TokenKind::LargeKeyword: os << "LargeKeyword"; break;
        case TokenKind::LetKeyword: os << "LetKeyword"; break;
        case TokenKind::LibListKeyword: os << "LibListKeyword"; break;
        case TokenKind::LibraryKeyword: os << "LibraryKeyword"; break;
        case TokenKind::LocalKeyword: os << "LocalKeyword"; break;
        case TokenKind::LocalParamKeyword: os << "LocalParamKeyword"; break;
        case TokenKind::LogicKeyword: os << "LogicKeyword"; break;
        case TokenKind::LongIntKeyword: os << "LongIntKeyword"; break;
        case TokenKind::MacromoduleKeyword: os << "MacromoduleKeyword"; break;
        case TokenKind::MatchesKeyword: os << "MatchesKeyword"; break;
        case TokenKind::MediumKeyword: os << "MediumKeyword"; break;
        case TokenKind::ModPortKeyword: os << "ModPortKeyword"; break;
        case TokenKind::ModuleKeyword: os << "ModuleKeyword"; break;
        case TokenKind::NandKeyword: os << "NandKeyword"; break;
        case TokenKind::NegEdgeKeyword: os << "NegEdgeKeyword"; break;
        case TokenKind::NetTypeKeyword: os << "NetTypeKeyword"; break;
        case TokenKind::NewKeyword: os << "NewKeyword"; break;
        case TokenKind::NextTimeKeyword: os << "NextTimeKeyword"; break;
        case TokenKind::NmosKeyword: os << "NmosKeyword"; break;
        case TokenKind::NorKeyword: os << "NorKeyword"; break;
        case TokenKind::NoShowCancelledKeyword: os << "NoShowCancelledKeyword"; break;
        case TokenKind::NotKeyword: os << "NotKeyword"; break;
        case TokenKind::NotIf0Keyword: os << "NotIf0Keyword"; break;
        case TokenKind::NotIf1Keyword: os << "NotIf1Keyword"; break;
        case TokenKind::NullKeyword: os << "NullKeyword"; break;
        case TokenKind::OrKeyword: os << "OrKeyword"; break;
        case TokenKind::OutputKeyword: os << "OutputKeyword"; break;
        case TokenKind::PackageKeyword: os << "PackageKeyword"; break;
        case TokenKind::PackedKeyword: os << "PackedKeyword"; break;
        case TokenKind::ParameterKeyword: os << "ParameterKeyword"; break;
        case TokenKind::PmosKeyword: os << "PmosKeyword"; break;
        case TokenKind::PosEdgeKeyword: os << "PosEdgeKeyword"; break;
        case TokenKind::PrimitiveKeyword: os << "PrimitiveKeyword"; break;
        case TokenKind::PriorityKeyword: os << "PriorityKeyword"; break;
        case TokenKind::ProgramKeyword: os << "ProgramKeyword"; break;
        case TokenKind::PropertyKeyword: os << "PropertyKeyword"; break;
        case TokenKind::ProtectedKeyword: os << "ProtectedKeyword"; break;
        case TokenKind::Pull0Keyword: os << "Pull0Keyword"; break;
        case TokenKind::Pull1Keyword: os << "Pull1Keyword"; break;
        case TokenKind::PullDownKeyword: os << "PullDownKeyword"; break;
        case TokenKind::PullUpKeyword: os << "PullUpKeyword"; break;
        case TokenKind::PulseStyleOnDetectKeyword: os << "PulseStyleOnDetectKeyword"; break;
        case TokenKind::PulseStyleOnEventKeyword: os << "PulseStyleOnEventKeyword"; break;
        case TokenKind::PureKeyword: os << "PureKeyword"; break;
        case TokenKind::RandKeyword: os << "RandKeyword"; break;
        case TokenKind::RandCKeyword: os << "RandCKeyword"; break;
        case TokenKind::RandCaseKeyword: os << "RandCaseKeyword"; break;
        case TokenKind::RandSequenceKeyword: os << "RandSequenceKeyword"; break;
        case TokenKind::RcmosKeyword: os << "RcmosKeyword"; break;
        case TokenKind::RealKeyword: os << "RealKeyword"; break;
        case TokenKind::RealTimeKeyword: os << "RealTimeKeyword"; break;
        case TokenKind::RefKeyword: os << "RefKeyword"; break;
        case TokenKind::RegKeyword: os << "RegKeyword"; break;
        case TokenKind::RejectOnKeyword: os << "RejectOnKeyword"; break;
        case TokenKind::ReleaseKeyword: os << "ReleaseKeyword"; break;
        case TokenKind::RepeatKeyword: os << "RepeatKeyword"; break;
        case TokenKind::RestrictKeyword: os << "RestrictKeyword"; break;
        case TokenKind::ReturnKeyword: os << "ReturnKeyword"; break;
        case TokenKind::RnmosKeyword: os << "RnmosKeyword"; break;
        case TokenKind::RpmosKeyword: os << "RpmosKeyword"; break;
        case TokenKind::RtranKeyword: os << "RtranKeyword"; break;
        case TokenKind::RtranIf0Keyword: os << "RtranIf0Keyword"; break;
        case TokenKind::RtranIf1Keyword: os << "RtranIf1Keyword"; break;
        case TokenKind::SAlwaysKeyword: os << "SAlwaysKeyword"; break;
        case TokenKind::SEventuallyKeyword: os << "SEventuallyKeyword"; break;
        case TokenKind::SNextTimeKeyword: os << "SNextTimeKeyword"; break;
        case TokenKind::SUntilKeyword: os << "SUntilKeyword"; break;
        case TokenKind::SUntilWithKeyword: os << "SUntilWithKeyword"; break;
        case TokenKind::ScalaredKeyword: os << "ScalaredKeyword"; break;
        case TokenKind::SequenceKeyword: os << "SequenceKeyword"; break;
        case TokenKind::ShortIntKeyword: os << "ShortIntKeyword"; break;
        case TokenKind::ShortRealKeyword: os << "ShortRealKeyword"; break;
        case TokenKind::ShowCancelledKeyword: os << "ShowCancelledKeyword"; break;
        case TokenKind::SignedKeyword: os << "SignedKeyword"; break;
        case TokenKind::SmallKeyword: os << "SmallKeyword"; break;
        case TokenKind::SoftKeyword: os << "SoftKeyword"; break;
        case TokenKind::SolveKeyword: os << "SolveKeyword"; break;
        case TokenKind::SpecifyKeyword: os << "SpecifyKeyword"; break;
        case TokenKind::SpecParamKeyword: os << "SpecParamKeyword"; break;
        case TokenKind::StaticKeyword: os << "StaticKeyword"; break;
        case TokenKind::StringKeyword: os << "StringKeyword"; break;
        case TokenKind::StrongKeyword: os << "StrongKeyword"; break;
        case TokenKind::Strong0Keyword: os << "Strong0Keyword"; break;
        case TokenKind::Strong1Keyword: os << "Strong1Keyword"; break;
        case TokenKind::StructKeyword: os << "StructKeyword"; break;
        case TokenKind::SuperKeyword: os << "SuperKeyword"; break;
        case TokenKind::Supply0Keyword: os << "Supply0Keyword"; break;
        case TokenKind::Supply1Keyword: os << "Supply1Keyword"; break;
        case TokenKind::SyncAcceptOnKeyword: os << "SyncAcceptOnKeyword"; break;
        case TokenKind::SyncRejectOnKeyword: os << "SyncRejectOnKeyword"; break;
        case TokenKind::TableKeyword: os << "TableKeyword"; break;
        case TokenKind::TaggedKeyword: os << "TaggedKeyword"; break;
        case TokenKind::TaskKeyword: os << "TaskKeyword"; break;
        case TokenKind::ThisKeyword: os << "ThisKeyword"; break;
        case TokenKind::ThroughoutKeyword: os << "ThroughoutKeyword"; break;
        case TokenKind::TimeKeyword: os << "TimeKeyword"; break;
        case TokenKind::TimePrecisionKeyword: os << "TimePrecisionKeyword"; break;
        case TokenKind::TimeUnitKeyword: os << "TimeUnitKeyword"; break;
        case TokenKind::TranKeyword: os << "TranKeyword"; break;
        case TokenKind::TranIf0Keyword: os << "TranIf0Keyword"; break;
        case TokenKind::TranIf1Keyword: os << "TranIf1Keyword"; break;
        case TokenKind::TriKeyword: os << "TriKeyword"; break;
        case TokenKind::Tri0Keyword: os << "Tri0Keyword"; break;
        case TokenKind::Tri1Keyword: os << "Tri1Keyword"; break;
        case TokenKind::TriAndKeyword: os << "TriAndKeyword"; break;
        case TokenKind::TriOrKeyword: os << "TriOrKeyword"; break;
        case TokenKind::TriRegKeyword: os << "TriRegKeyword"; break;
        case TokenKind::TypeKeyword: os << "TypeKeyword"; break;
        case TokenKind::TypedefKeyword: os << "TypedefKeyword"; break;
        case TokenKind::UnionKeyword: os << "UnionKeyword"; break;
        case TokenKind::UniqueKeyword: os << "UniqueKeyword"; break;
        case TokenKind::Unique0Keyword: os << "Unique0Keyword"; break;
        case TokenKind::UnsignedKeyword: os << "UnsignedKeyword"; break;
        case TokenKind::UntilKeyword: os << "UntilKeyword"; break;
        case TokenKind::UntilWithKeyword: os << "UntilWithKeyword"; break;
        case TokenKind::UntypedKeyword: os << "UntypedKeyword"; break;
        case TokenKind::UseKeyword: os << "UseKeyword"; break;
        case TokenKind::UWireKeyword: os << "UWireKeyword"; break;
        case TokenKind::VarKeyword: os << "VarKeyword"; break;
        case TokenKind::VectoredKeyword: os << "VectoredKeyword"; break;
        case TokenKind::VirtualKeyword: os << "VirtualKeyword"; break;
        case TokenKind::VoidKeyword: os << "VoidKeyword"; break;
        case TokenKind::WaitKeyword: os << "WaitKeyword"; break;
        case TokenKind::WaitOrderKeyword: os << "WaitOrderKeyword"; break;
        case TokenKind::WAndKeyword: os << "WAndKeyword"; break;
        case TokenKind::WeakKeyword: os << "WeakKeyword"; break;
        case TokenKind::Weak0Keyword: os << "Weak0Keyword"; break;
        case TokenKind::Weak1Keyword: os << "Weak1Keyword"; break;
        case TokenKind::WhileKeyword: os << "WhileKeyword"; break;
        case TokenKind::WildcardKeyword: os << "WildcardKeyword"; break;
        case TokenKind::WireKeyword: os << "WireKeyword"; break;
        case TokenKind::WithKeyword: os << "WithKeyword"; break;
        case TokenKind::WithinKeyword: os << "WithinKeyword"; break;
        case TokenKind::WOrKeyword: os << "WOrKeyword"; break;
        case TokenKind::XnorKeyword: os << "XnorKeyword"; break;
        case TokenKind::XorKeyword: os << "XorKeyword"; break;
        case TokenKind::UnitSystemName: os << "UnitSystemName"; break;
        case TokenKind::RootSystemName: os << "RootSystemName"; break;
        case TokenKind::Directive: os << "Directive"; break;
        case TokenKind::EndOfDirective: os << "EndOfDirective"; break;
        case TokenKind::IncludeFileName: os << "IncludeFileName"; break;
        case TokenKind::MacroUsage: os << "MacroUsage"; break;
        case TokenKind::MacroQuote: os << "MacroQuote"; break;
        case TokenKind::MacroEscapedQuote: os << "MacroEscapedQuote"; break;
        case TokenKind::MacroPaste: os << "MacroPaste"; break;
        default: os << "<unknown>"; break;
    }
    return os;
}

}