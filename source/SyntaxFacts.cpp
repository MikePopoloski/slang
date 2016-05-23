#include "SyntaxNode.h"

#include "Token.h"

namespace slang {

SyntaxKind getUnaryPrefixExpression(TokenKind kind) {
    switch (kind) {
        case TokenKind::Plus: return SyntaxKind::UnaryPlusExpression;
        case TokenKind::Minus: return SyntaxKind::UnaryMinusExpression;
        case TokenKind::And: return SyntaxKind::UnaryBitwiseAndExpression;
        case TokenKind::TildeAnd: return SyntaxKind::UnaryBitwiseNandExpression;
        case TokenKind::Or: return SyntaxKind::UnaryBitwiseOrExpression;
        case TokenKind::TildeOr: return SyntaxKind::UnaryBitwiseNorExpression;
        case TokenKind::Xor: return SyntaxKind::UnaryBitwiseXorExpression;
        case TokenKind::XorTilde:
        case TokenKind::TildeXor:
            return SyntaxKind::UnaryBitwiseXnorExpression;
        case TokenKind::DoublePlus: return SyntaxKind::UnaryPreincrementExpression;
        case TokenKind::DoubleMinus: return SyntaxKind::UnaryPredecrementExpression;
        case TokenKind::Tilde: return SyntaxKind::UnaryBitwiseNotExpression;
        case TokenKind::Exclamation: return SyntaxKind::UnaryLogicalNotExpression;
        default:
            return SyntaxKind::Unknown;
    }
}

SyntaxKind getUnaryPostfixExpression(TokenKind kind) {
    switch (kind) {
        case TokenKind::DoublePlus: return SyntaxKind::PostincrementExpression;
        case TokenKind::DoubleMinus: return SyntaxKind::PostdecrementExpression;
        default: return SyntaxKind::Unknown;
    }
}

SyntaxKind getLiteralExpression(TokenKind kind) {
    switch (kind) {
        case TokenKind::StringLiteral: return SyntaxKind::StringLiteralExpression;
        case TokenKind::IntegerLiteral: return SyntaxKind::IntegerLiteralExpression;
        case TokenKind::UnbasedUnsizedLiteral: return SyntaxKind::UnbasedUnsizedLiteralExpression;
        case TokenKind::RealLiteral: return SyntaxKind::RealLiteralExpression;
        case TokenKind::TimeLiteral: return SyntaxKind::TimeLiteralExpression;
        case TokenKind::NullKeyword: return SyntaxKind::NullLiteralExpression;
        case TokenKind::Dollar: return SyntaxKind::WildcardLiteralExpression;
        case TokenKind::OneStep: return SyntaxKind::OneStepLiteralExpression;
        default: return SyntaxKind::Unknown;
    }
}

SyntaxKind getBinaryExpression(TokenKind kind) {
    switch (kind) {
        case TokenKind::Plus: return SyntaxKind::AddExpression;
        case TokenKind::Minus: return SyntaxKind::SubtractExpression;
        case TokenKind::Star: return SyntaxKind::MultiplyExpression;
        case TokenKind::Slash: return SyntaxKind::DivideExpression;
        case TokenKind::Percent: return SyntaxKind::ModExpression;
        case TokenKind::DoubleStar: return SyntaxKind::PowerExpression;
        case TokenKind::DoubleEquals: return SyntaxKind::EqualityExpression;
        case TokenKind::ExclamationEquals: return SyntaxKind::InequalityExpression;
        case TokenKind::TripleEquals: return SyntaxKind::CaseEqualityExpression;
        case TokenKind::ExclamationDoubleEquals: return SyntaxKind::CaseInequalityExpression;
        case TokenKind::DoubleEqualsQuestion: return SyntaxKind::WildcardEqualityExpression;
        case TokenKind::ExclamationEqualsQuestion: return SyntaxKind::WildcardInequalityExpression;
        case TokenKind::DoubleAnd: return SyntaxKind::LogicalAndExpression;
        case TokenKind::DoubleOr: return SyntaxKind::LogicalOrExpression;
        case TokenKind::MinusArrow: return SyntaxKind::LogicalImplicationExpression;
        case TokenKind::LessThanMinusArrow: return SyntaxKind::LogicalEquivalenceExpression;
        case TokenKind::LessThan: return SyntaxKind::LessThanExpression;
        case TokenKind::LessThanEquals: return SyntaxKind::LessThanEqualExpression;
        case TokenKind::GreaterThan: return SyntaxKind::GreaterThanExpression;
        case TokenKind::GreaterThanEquals: return SyntaxKind::GreaterThanEqualExpression;
        case TokenKind::And: return SyntaxKind::BinaryAndExpression;
        case TokenKind::Or: return SyntaxKind::BinaryOrExpression;
        case TokenKind::Xor: return SyntaxKind::BinaryXorExpression;
        case TokenKind::XorTilde: return SyntaxKind::BinaryXnorExpression;
        case TokenKind::TildeXor: return SyntaxKind::BinaryXnorExpression;
        case TokenKind::RightShift: return SyntaxKind::LogicalShiftRightExpression;
        case TokenKind::TripleRightShift: return SyntaxKind::ArithmeticShiftRightExpression;
        case TokenKind::LeftShift: return SyntaxKind::LogicalShiftLeftExpression;
        case TokenKind::TripleLeftShift: return SyntaxKind::ArithmeticShiftLeftExpression;
        case TokenKind::InsideKeyword: return SyntaxKind::InsideExpression;
        case TokenKind::Equals: return SyntaxKind::AssignmentExpression;
        case TokenKind::PlusEqual: return SyntaxKind::AddAssignmentExpression;
        case TokenKind::MinusEqual: return SyntaxKind::SubtractAssignmentExpression;
        case TokenKind::StarEqual: return SyntaxKind::MultiplyAssignmentExpression;
        case TokenKind::SlashEqual: return SyntaxKind::DivideAssignmentExpression;
        case TokenKind::PercentEqual: return SyntaxKind::ModAssignmentExpression;
        case TokenKind::AndEqual: return SyntaxKind::AndAssignmentExpression;
        case TokenKind::OrEqual: return SyntaxKind::OrAssignmentExpression;
        case TokenKind::XorEqual: return SyntaxKind::XorAssignmentExpression;
        case TokenKind::LeftShiftEqual: return SyntaxKind::LogicalLeftShiftAssignmentExpression;
        case TokenKind::TripleLeftShiftEqual: return SyntaxKind::ArithmeticLeftShiftAssignmentExpression;
        case TokenKind::RightShiftEqual: return SyntaxKind::LogicalRightShiftAssignmentExpression;
        case TokenKind::TripleRightShiftEqual: return SyntaxKind::ArithmeticRightShiftAssignmentExpression;
        default: return SyntaxKind::Unknown;
    }
}

SyntaxKind getKeywordNameExpression(TokenKind kind) {
    switch (kind) {
        case TokenKind::UnitSystemName: return SyntaxKind::UnitScope;
        case TokenKind::RootSystemName: return SyntaxKind::RootScope;
        case TokenKind::LocalKeyword: return SyntaxKind::LocalScope;
        case TokenKind::ThisKeyword: return SyntaxKind::ThisHandle;
        case TokenKind::SuperKeyword: return SyntaxKind::SuperHandle;
        case TokenKind::UniqueKeyword: return SyntaxKind::ArrayUniqueMethod;
        case TokenKind::AndKeyword: return SyntaxKind::ArrayAndMethod;
        case TokenKind::OrKeyword: return SyntaxKind::ArrayOrMethod;
        case TokenKind::XorKeyword: return SyntaxKind::ArrayXorMethod;
        default: return SyntaxKind::Unknown;
    }
}

int getPrecedence(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::AssignmentExpression:
        case SyntaxKind::AddAssignmentExpression:
        case SyntaxKind::SubtractAssignmentExpression:
        case SyntaxKind::MultiplyAssignmentExpression:
        case SyntaxKind::DivideAssignmentExpression:
        case SyntaxKind::ModAssignmentExpression:
        case SyntaxKind::AndAssignmentExpression:
        case SyntaxKind::OrAssignmentExpression:
        case SyntaxKind::XorAssignmentExpression:
        case SyntaxKind::LogicalLeftShiftAssignmentExpression:
        case SyntaxKind::LogicalRightShiftAssignmentExpression:
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression:
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression:
        case SyntaxKind::NonblockingAssignmentExpression:
            return 1;
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            return 2;
        case SyntaxKind::LogicalOrExpression:
            return 3;
        case SyntaxKind::LogicalAndExpression:
            return 4;
        case SyntaxKind::BinaryOrExpression:
            return 5;
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
            return 6;
        case SyntaxKind::BinaryAndExpression:
            return 7;
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
        case SyntaxKind::CaseEqualityExpression:
        case SyntaxKind::CaseInequalityExpression:
        case SyntaxKind::WildcardEqualityExpression:
        case SyntaxKind::WildcardInequalityExpression:
            return 8;
        case SyntaxKind::LessThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::InsideExpression:
            return 9;
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
            return 10;
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
            return 11;
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::DivideExpression:
        case SyntaxKind::ModExpression:
            return 12;
        case SyntaxKind::PowerExpression:
            return 13;
        case SyntaxKind::UnaryPlusExpression:
        case SyntaxKind::UnaryMinusExpression:
        case SyntaxKind::UnaryLogicalNotExpression:
        case SyntaxKind::UnaryBitwiseNotExpression:
        case SyntaxKind::UnaryBitwiseAndExpression:
        case SyntaxKind::UnaryBitwiseNandExpression:
        case SyntaxKind::UnaryBitwiseOrExpression:
        case SyntaxKind::UnaryBitwiseNorExpression:
        case SyntaxKind::UnaryBitwiseXorExpression:
        case SyntaxKind::UnaryBitwiseXnorExpression:
        case SyntaxKind::UnaryPreincrementExpression:
        case SyntaxKind::UnaryPredecrementExpression:
            return 14;
        default:
            return 0;
    }
}

bool isRightAssociative(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            return true;
        default:
            return false;
    }
}

bool isPossibleDataType(TokenKind kind) {
    switch (kind) {
        case TokenKind::BitKeyword:
        case TokenKind::LogicKeyword:
        case TokenKind::RegKeyword:
        case TokenKind::ByteKeyword:
        case TokenKind::ShortIntKeyword:
        case TokenKind::IntKeyword:
        case TokenKind::LongIntKeyword:
        case TokenKind::IntegerKeyword:
        case TokenKind::TimeKeyword:
        case TokenKind::ShortRealKeyword:
        case TokenKind::RealKeyword:
        case TokenKind::RealTimeKeyword:
        case TokenKind::StringKeyword:
        case TokenKind::ConstKeyword:
        case TokenKind::SignedKeyword:
        case TokenKind::UnsignedKeyword:
        case TokenKind::StructKeyword:
        case TokenKind::UnionKeyword:
        case TokenKind::EnumKeyword:
        case TokenKind::CHandleKeyword:
        case TokenKind::VirtualKeyword:
        case TokenKind::EventKeyword:
        case TokenKind::TypeKeyword:
        case TokenKind::VoidKeyword:
        case TokenKind::Identifier:
        case TokenKind::UnitSystemName:
            return true;
        default:
            return false;
    }
}

bool isPossibleExpression(TokenKind kind) {
    switch (kind) {
        case TokenKind::TaggedKeyword:
        case TokenKind::StringLiteral:
        case TokenKind::IntegerLiteral:
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::IntegerBase:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
        case TokenKind::NullKeyword:
        case TokenKind::Dollar:
        case TokenKind::SystemIdentifier:
        case TokenKind::LocalKeyword:
        case TokenKind::OpenParenthesis:
        case TokenKind::OpenBrace:
        case TokenKind::UnitSystemName:
        case TokenKind::ThisKeyword:
        case TokenKind::SuperKeyword:
        case TokenKind::Identifier:
        case TokenKind::RootSystemName:
        case TokenKind::Hash:
        case TokenKind::TypeKeyword:
        case TokenKind::ApostropheOpenBrace:
            // expressions can't actually start with these, but we'll allow it
            // to provide good error handling
        case TokenKind::DoubleColon:
        case TokenKind::Question:
        case TokenKind::MatchesKeyword:
        case TokenKind::TripleAnd:
        case TokenKind::InsideKeyword:
            return true;
        default:
            break;
    }

    if (isPossibleDataType(kind))
        return true;

    SyntaxKind opKind = getUnaryPrefixExpression(kind);
    if (opKind != SyntaxKind::Unknown)
        return true;

    opKind = getBinaryExpression(kind);
    if (opKind != SyntaxKind::Unknown)
        return true;

    return false;
}

bool isPossibleStatement(TokenKind kind) {
    switch (kind) {
        case TokenKind::Identifier:
        case TokenKind::ThisKeyword:
        case TokenKind::SuperKeyword:
        case TokenKind::UnitSystemName:
        case TokenKind::RootSystemName:
        case TokenKind::SystemIdentifier:
        case TokenKind::OpenBrace:
        case TokenKind::ApostropheOpenBrace:
        case TokenKind::AssignKeyword:
        case TokenKind::DeassignKeyword:
        case TokenKind::ForceKeyword:
        case TokenKind::ReleaseKeyword:
        case TokenKind::UniqueKeyword:
        case TokenKind::Unique0Keyword:
        case TokenKind::PriorityKeyword:
        case TokenKind::CaseKeyword:
        case TokenKind::CaseXKeyword:
        case TokenKind::CaseZKeyword:
        case TokenKind::IfKeyword:
        case TokenKind::DoublePlus:
        case TokenKind::DoubleMinus:
        case TokenKind::VoidKeyword:
        case TokenKind::DisableKeyword:
        case TokenKind::MinusArrow:
        case TokenKind::OrMinusDoubleArrow:
        case TokenKind::ForeverKeyword:
        case TokenKind::RepeatKeyword:
        case TokenKind::WhileKeyword:
        case TokenKind::ForKeyword:
        case TokenKind::DoKeyword:
        case TokenKind::ForeachKeyword:
        case TokenKind::ReturnKeyword:
        case TokenKind::BreakKeyword:
        case TokenKind::ContinueKeyword:
        case TokenKind::ForkKeyword:
        case TokenKind::Hash:
        case TokenKind::DoubleHash:
        case TokenKind::At:
        case TokenKind::AtStar:
        case TokenKind::BeginKeyword:
        case TokenKind::WaitKeyword:
        case TokenKind::WaitOrderKeyword:
        case TokenKind::AssertKeyword:
        case TokenKind::AssumeKeyword:
        case TokenKind::CoverKeyword:
        case TokenKind::RestrictKeyword:
        case TokenKind::RandSequenceKeyword:
        case TokenKind::RandCaseKeyword:
        case TokenKind::ExpectKeyword:
        case TokenKind::OpenParenthesisStar:
        case TokenKind::Semicolon:
            return true;
        default:
            return false;
    }
}

SyntaxKind getIntegerType(TokenKind kind) {
    switch (kind) {
        case TokenKind::BitKeyword: return SyntaxKind::BitType;
        case TokenKind::LogicKeyword: return SyntaxKind::LogicType;
        case TokenKind::RegKeyword: return SyntaxKind::RegType;
        case TokenKind::ByteKeyword: return SyntaxKind::ByteType;
        case TokenKind::ShortIntKeyword: return SyntaxKind::ShortIntType;
        case TokenKind::IntKeyword: return SyntaxKind::IntType;
        case TokenKind::LongIntKeyword: return SyntaxKind::LongIntType;
        case TokenKind::IntegerKeyword: return SyntaxKind::IntegerType;
        case TokenKind::TimeKeyword: return SyntaxKind::TimeType;
        default: return SyntaxKind::Unknown;
    }
}

SyntaxKind getKeywordType(TokenKind kind) {
    switch (kind) {
        case TokenKind::ShortRealKeyword: return SyntaxKind::ShortRealType;
        case TokenKind::RealKeyword: return SyntaxKind::RealType;
        case TokenKind::RealTimeKeyword: return SyntaxKind::RealTimeType;
        case TokenKind::StringKeyword: return SyntaxKind::StringType;
        case TokenKind::CHandleKeyword: return SyntaxKind::CHandleType;
        case TokenKind::EventKeyword: return SyntaxKind::EventType;
        case TokenKind::VoidKeyword: return SyntaxKind::VoidType;
        default: return SyntaxKind::Unknown;
    }
}

SyntaxKind getProceduralBlockKind(TokenKind kind) {
    switch (kind) {
        case TokenKind::InitialKeyword: return SyntaxKind::InitialBlock;
        case TokenKind::FinalKeyword: return SyntaxKind::FinalBlock;
        case TokenKind::AlwaysKeyword: return SyntaxKind::AlwaysBlock;
        case TokenKind::AlwaysCombKeyword: return SyntaxKind::AlwaysCombBlock;
        case TokenKind::AlwaysFFKeyword: return SyntaxKind::AlwaysFFBlock;
        case TokenKind::AlwaysLatchKeyword: return SyntaxKind::AlwaysLatchBlock;
        default: return SyntaxKind::Unknown;
    }
}

SyntaxKind getModuleHeaderKind(TokenKind kind) {
    switch (kind) {
        case TokenKind::ModuleKeyword: return SyntaxKind::ModuleHeader;
        case TokenKind::MacromoduleKeyword: return SyntaxKind::ModuleHeader;
        case TokenKind::ProgramKeyword: return SyntaxKind::ProgramHeader;
        case TokenKind::InterfaceKeyword: return SyntaxKind::InterfaceHeader;
        default: return SyntaxKind::Unknown;
    }
}

SyntaxKind getModuleDeclarationKind(TokenKind kind) {
    switch (kind) {
        case TokenKind::ModuleKeyword: return SyntaxKind::ModuleDeclaration;
        case TokenKind::MacromoduleKeyword: return SyntaxKind::ModuleDeclaration;
        case TokenKind::ProgramKeyword: return SyntaxKind::ProgramDeclaration;
        case TokenKind::InterfaceKeyword: return SyntaxKind::InterfaceDeclaration;
        default: return SyntaxKind::Unknown;
    }
}

TokenKind getModuleEndKind(TokenKind kind) {
    switch (kind) {
        case TokenKind::ModuleKeyword: return TokenKind::EndModuleKeyword;
        case TokenKind::MacromoduleKeyword: return TokenKind::EndModuleKeyword;
        case TokenKind::ProgramKeyword: return TokenKind::EndProgramKeyword;
        case TokenKind::InterfaceKeyword: return TokenKind::EndInterfaceKeyword;
        default: return TokenKind::Unknown;
    }
}

bool isNetType(TokenKind kind) {
    switch (kind) {
        case TokenKind::Supply0Keyword:
        case TokenKind::Supply1Keyword:
        case TokenKind::TriKeyword:
        case TokenKind::TriAndKeyword:
        case TokenKind::TriOrKeyword:
        case TokenKind::TriRegKeyword:
        case TokenKind::Tri0Keyword:
        case TokenKind::Tri1Keyword:
        case TokenKind::UWireKeyword:
        case TokenKind::WireKeyword:
        case TokenKind::WAndKeyword:
        case TokenKind::WOrKeyword:
            return true;
        default:
            return false;
    }
}

bool isPortDirection(TokenKind kind) {
    switch (kind) {
        case TokenKind::InputKeyword:
        case TokenKind::OutputKeyword:
        case TokenKind::InOutKeyword:
        case TokenKind::RefKeyword:
            return true;
        default:
            return false;
    }
}

bool isPossibleArgument(TokenKind kind) {
    // allow a comma here to handle cases like:  foo(, 3);
    switch (kind) {
        case TokenKind::Dot:
        case TokenKind::Comma:
            return true;
        default:
            return isPossibleExpression(kind);
    }
}

bool isPossibleNonAnsiPort(TokenKind kind) {
    switch (kind) {
        case TokenKind::Dot:
        case TokenKind::Comma:
        case TokenKind::Identifier:
        case TokenKind::OpenBrace:
            return true;
        default:
            return false;
    }
}

bool isPossibleAnsiPort(TokenKind kind) {
    switch (kind) {
        case TokenKind::InterconnectKeyword:
        case TokenKind::InterfaceKeyword:
        case TokenKind::Identifier:
        case TokenKind::Dot:
        case TokenKind::Comma:
        case TokenKind::InputKeyword:
        case TokenKind::OutputKeyword:
        case TokenKind::InOutKeyword:
        case TokenKind::RefKeyword:
        case TokenKind::VarKeyword:
            return true;
        default:
            return isNetType(kind) || isPossibleDataType(kind);
    }
}

bool isComma(TokenKind kind) {
    return kind == TokenKind::Comma;
}

bool isSemicolon(TokenKind kind) {
    return kind == TokenKind::Semicolon;
}

bool isCloseBrace(TokenKind kind) {
    return kind == TokenKind::CloseBrace;
}

bool isIdentifierOrComma(TokenKind kind) {
    return kind == TokenKind::Identifier || kind == TokenKind::Comma;
}

bool isPossibleExpressionOrComma(TokenKind kind) {
    return kind == TokenKind::Comma || isPossibleExpression(kind);
}

bool isPossibleExpressionOrTripleAnd(TokenKind kind) {
    return kind == TokenKind::TripleAnd || isPossibleExpression(kind);
}

bool isPossibleInsideElement(TokenKind kind) {
    switch (kind) {
        case TokenKind::OpenBracket:
        case TokenKind::Comma:
            return true;
        default:
            return isPossibleExpression(kind);
    }
}

bool isPossiblePattern(TokenKind kind) {
    switch (kind) {
        case TokenKind::Dot:
        case TokenKind::DotStar:
        case TokenKind::ApostropheOpenBrace:
            return true;
        default:
            return isPossibleExpression(kind);
    }
}

bool isPossibleDelayOrEventControl(TokenKind kind) {
    switch (kind) {
        case TokenKind::Hash:
        case TokenKind::At:
        case TokenKind::AtStar:
        case TokenKind::RepeatKeyword:
            return true;
        default:
            return false;
    }
}

bool isPossibleParameter(TokenKind kind) {
    switch (kind) {
        case TokenKind::ParameterKeyword:
        case TokenKind::LocalParamKeyword:
        case TokenKind::TypeKeyword:
        case TokenKind::Comma:
            return true;
        default:
            return isPossibleDataType(kind);
    }
}

bool isPossiblePortConnection(TokenKind kind) {
    switch (kind) {
        case TokenKind::OpenParenthesisStar:
        case TokenKind::DotStar:
        case TokenKind::Dot:
        case TokenKind::Comma:
            return true;
        default:
            return isPossibleExpression(kind);
    }
}

bool isPossibleVectorDigit(TokenKind kind) {
    switch (kind) {
        case TokenKind::IntegerLiteral:
        case TokenKind::Question:
        case TokenKind::RealLiteral:
        case TokenKind::Identifier:
            return true;
        default:
            return false;
    }
}

bool isEndKeyword(TokenKind kind) {
    switch (kind) {
        case TokenKind::EndKeyword:
        case TokenKind::EndCaseKeyword:
        case TokenKind::EndCheckerKeyword:
        case TokenKind::EndClassKeyword:
        case TokenKind::EndClockingKeyword:
        case TokenKind::EndConfigKeyword:
        case TokenKind::EndFunctionKeyword:
        case TokenKind::EndGenerateKeyword:
        case TokenKind::EndGroupKeyword:
        case TokenKind::EndInterfaceKeyword:
        case TokenKind::EndModuleKeyword:
        case TokenKind::EndPackageKeyword:
        case TokenKind::EndPrimitiveKeyword:
        case TokenKind::EndProgramKeyword:
        case TokenKind::EndPropertyKeyword:
        case TokenKind::EndSpecifyKeyword:
        case TokenKind::EndSequenceKeyword:
        case TokenKind::EndTableKeyword:
        case TokenKind::EndTaskKeyword:
            return true;
        default:
            return false;
    }
}

bool isDeclarationModifier(TokenKind kind) {
    switch (kind) {
        case TokenKind::ConstKeyword:
        case TokenKind::VarKeyword:
        case TokenKind::StaticKeyword:
        case TokenKind::AutomaticKeyword:
            return true;
        default:
            return false;
    }
}

bool isEndOfParenList(TokenKind kind) {
    return kind == TokenKind::CloseParenthesis || kind == TokenKind::Semicolon;
}

bool isEndOfBracedList(TokenKind kind) {
    return kind == TokenKind::CloseBrace || kind == TokenKind::Semicolon;
}

bool isEndOfCaseItem(TokenKind kind) {
    return kind == TokenKind::Colon || kind == TokenKind::Semicolon;
}

bool isEndOfConditionalPredicate(TokenKind kind) {
    return kind == TokenKind::Question || kind == TokenKind::CloseParenthesis || kind == TokenKind::BeginKeyword || kind == TokenKind::Semicolon;
}

bool isEndOfAttribute(TokenKind kind) {
    switch (kind) {
        case TokenKind::StarCloseParenthesis:
            // these indicate a missing *) somewhere
        case TokenKind::Semicolon:
        case TokenKind::PrimitiveKeyword:
        case TokenKind::ProgramKeyword:
        case TokenKind::InterfaceKeyword:
        case TokenKind::PackageKeyword:
        case TokenKind::CheckerKeyword:
        case TokenKind::GenerateKeyword:
        case TokenKind::ModuleKeyword:
        case TokenKind::ClassKeyword:
            return true;
        default:
            return false;
    }
}

bool isEndOfParameterList(TokenKind kind) {
    return kind == TokenKind::CloseParenthesis || kind == TokenKind::OpenParenthesis || kind == TokenKind::Semicolon;
}

bool isNotInType(TokenKind kind) {
    switch (kind) {
        case TokenKind::Semicolon:
        case TokenKind::EndOfFile:
            return true;
        default:
            return isEndKeyword(kind);
    }
}

bool isNotInPortReference(TokenKind kind) {
    return kind == TokenKind::Semicolon || kind == TokenKind::EndOfFile;
}

}
