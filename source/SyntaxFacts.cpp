#include <cstdint>
#include <memory>
#include <string>
#include <algorithm>

#include "BumpAllocator.h"
#include "StringRef.h"
#include "Token.h"
#include "SyntaxNode.h"

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

SyntaxKind getAssignmentStatement(TokenKind kind) {
    switch (kind) {
        case TokenKind::Equals: return SyntaxKind::BlockingAssignmentStatement;
        case TokenKind::PlusEqual: return SyntaxKind::AddAssignmentStatement;
        case TokenKind::MinusEqual: return SyntaxKind::SubtractAssignmentStatement;
        case TokenKind::StarEqual: return SyntaxKind::MultiplyAssignmentStatement;
        case TokenKind::SlashEqual: return SyntaxKind::DivideAssignmentStatement;
        case TokenKind::PercentEqual: return SyntaxKind::ModAssignmentStatement;
        case TokenKind::AndEqual: return SyntaxKind::AndAssignmentStatement;
        case TokenKind::OrEqual: return SyntaxKind::OrAssignmentStatement;
        case TokenKind::XorEqual: return SyntaxKind::XorAssignmentStatement;
        case TokenKind::LeftShiftEqual: return SyntaxKind::LogicalLeftShiftAssignmentStatement;
        case TokenKind::TripleLeftShiftEqual: return SyntaxKind::ArithmeticLeftShiftAssignmentStatement;
        case TokenKind::RightShiftEqual: return SyntaxKind::LogicalRightShiftAssignmentStatement;
        case TokenKind::TripleRightShiftEqual: return SyntaxKind::ArithmeticRightShiftAssignmentStatement;
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
        case SyntaxKind::LogicalNotExpression:
        case SyntaxKind::BitwiseNotExpression:
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

std::ostream& operator<<(std::ostream& os, SyntaxKind kind) {
#define CASE(name) case SyntaxKind::name: os << #name; break
    switch (kind) {
        CASE(Unknown);
        CASE(List);
        CASE(BeginKeywordsDirective);
        CASE(CellDefineDirective);
        CASE(DefaultNetTypeDirective);
        CASE(DefineDirective);
        CASE(ElseDirective);
        CASE(ElseIfDirective);
        CASE(EndKeywordsDirective);
        CASE(EndCellDefineDirective);
        CASE(EndIfDirective);
        CASE(IfDefDirective);
        CASE(IfNDefDirective);
        CASE(IncludeDirective);
        CASE(LineDirective);
        CASE(NoUnconnectedDriveDirective);
        CASE(PragmaDirective);
        CASE(ResetAllDirective);
        CASE(TimescaleDirective);
        CASE(UnconnectedDriveDirective);
        CASE(UndefDirective);
        CASE(UndefineAllDirective);
        CASE(MacroUsage);
        CASE(MacroFormalArgumentList);
        CASE(MacroFormalArgument);
        CASE(MacroArgumentDefault);
        CASE(AttributeSpec);
        CASE(AttributeInstance);
        CASE(OrderedArgument);
        CASE(NamedArgument);
        CASE(ArgumentList);
        CASE(ParameterValueAssignment);
        CASE(VariablePattern);
        CASE(WildcardPattern);
        CASE(ExpressionPattern);
        CASE(TaggedPattern);
        CASE(OrderedStructurePatternMember);
        CASE(NamedStructurePatternMember);
        CASE(StructurePattern);
        CASE(MatchesClause);
        CASE(ConditionalPattern);
        CASE(ConditionalPredicate);
        CASE(UnaryPlusExpression);
        CASE(UnaryMinusExpression);
        CASE(UnaryBitwiseAndExpression);
        CASE(UnaryBitwiseNandExpression);
        CASE(UnaryBitwiseOrExpression);
        CASE(UnaryBitwiseNorExpression);
        CASE(UnaryBitwiseXorExpression);
        CASE(UnaryBitwiseXnorExpression);
        CASE(UnaryPreincrementExpression);
        CASE(UnaryPredecrementExpression);
        CASE(LogicalNotExpression);
        CASE(BitwiseNotExpression);
        CASE(NullLiteralExpression);
        CASE(StringLiteralExpression);
        CASE(IntegerLiteralExpression);
        CASE(RealLiteralExpression);
        CASE(TimeLiteralExpression);
        CASE(WildcardLiteralExpression);
        CASE(OneStepLiteralExpression);
        CASE(ParenthesizedExpression);
        CASE(MinTypMaxExpression);
        CASE(EmptyQueueExpression);
        CASE(ConcatenationExpression);
        CASE(MultipleConcatenationExpression);
        CASE(StreamingConcatenationExpression);
        CASE(StreamExpression);
        CASE(StreamExpressionWithRange);
        CASE(NewClassExpression);
        CASE(NewArrayExpression);
        CASE(BitSelect);
        CASE(SimpleRangeSelect);
        CASE(AscendingRangeSelect);
        CASE(DescendingRangeSelect);
        CASE(ElementSelect);
        CASE(ElementSelectExpression);
        CASE(MemberAccessExpression);
        CASE(InvocationExpression);
        CASE(PostincrementExpression);
        CASE(PostdecrementExpression);
        CASE(AddExpression);
        CASE(SubtractExpression);
        CASE(MultiplyExpression);
        CASE(DivideExpression);
        CASE(PowerExpression);
        CASE(ModExpression);
        CASE(EqualityExpression);
        CASE(InequalityExpression);
        CASE(CaseEqualityExpression);
        CASE(CaseInequalityExpression);
        CASE(WildcardEqualityExpression);
        CASE(WildcardInequalityExpression);
        CASE(LessThanExpression);
        CASE(LessThanEqualExpression);
        CASE(GreaterThanExpression);
        CASE(GreaterThanEqualExpression);
        CASE(LogicalAndExpression);
        CASE(LogicalOrExpression);
        CASE(BinaryAndExpression);
        CASE(BinaryOrExpression);
        CASE(BinaryXorExpression);
        CASE(BinaryXnorExpression);
        CASE(LogicalImplicationExpression);
        CASE(LogicalEquivalenceExpression);
        CASE(LogicalShiftLeftExpression);
        CASE(LogicalShiftRightExpression);
        CASE(ArithmeticShiftLeftExpression);
        CASE(ArithmeticShiftRightExpression);
        CASE(TaggedUnionExpression);
        CASE(InsideExpression);
        CASE(ConditionalExpression);
        CASE(AssignmentExpression);
        CASE(AddAssignmentExpression);
        CASE(SubtractAssignmentExpression);
        CASE(MultiplyAssignmentExpression);
        CASE(DivideAssignmentExpression);
        CASE(ModAssignmentExpression);
        CASE(AndAssignmentExpression);
        CASE(OrAssignmentExpression);
        CASE(XorAssignmentExpression);
        CASE(LogicalLeftShiftAssignmentExpression);
        CASE(LogicalRightShiftAssignmentExpression);
        CASE(ArithmeticLeftShiftAssignmentExpression);
        CASE(ArithmeticRightShiftAssignmentExpression);
        CASE(LocalScope);
        CASE(UnitScope);
        CASE(RootScope);
        CASE(IdentifierName);
        CASE(IdentifierSelectName);
        CASE(ClassName);
        CASE(ScopedName);
        CASE(SystemName);
        CASE(ThisHandle);
        CASE(SuperHandle);
        CASE(ArrayUniqueMethod);
        CASE(ArrayAndMethod);
        CASE(ArrayOrMethod);
        CASE(ArrayXorMethod);
        CASE(ClassScope);
        CASE(DelayControl);
        CASE(CycleDelay);
        CASE(EventControl);
        CASE(IffClause);
        CASE(SignalEventExpression);
        CASE(BinaryEventExpression);
        CASE(ParenthesizedEventExpression);
        CASE(ImplicitEventControl);
        CASE(ParenImplicitEventControl);
        CASE(EventControlWithExpression);
        CASE(RepeatedEventControl);
        CASE(RangeDimensionSpecifier);
        CASE(DataTypeDimensionSpecifier);
        CASE(WildcardDimensionSpecifier);
        CASE(ColonExpressionClause);
        CASE(QueueDimensionSpecifier);
        CASE(VariableDimension);
        CASE(EqualsValueClause);
        CASE(VariableDeclarator);
        CASE(DataDeclaration);
        CASE(PackageImportItem);
        CASE(PackageImportDeclaration);
        CASE(ParameterDeclaration);
        CASE(TypeParameterDeclaration);
        CASE(BitType);
        CASE(LogicType);
        CASE(RegType);
        CASE(ByteType);
        CASE(ShortIntType);
        CASE(IntType);
        CASE(LongIntType);
        CASE(IntegerType);
        CASE(TimeType);
        CASE(ShortRealType);
        CASE(RealType);
        CASE(RealTimeType);
        CASE(StructType);
        CASE(UnionType);
        CASE(EnumType);
        CASE(StringType);
        CASE(CHandleType);
        CASE(VirtualInterfaceType);
        CASE(NamedType);
        CASE(EventType);
        CASE(VoidType);
        CASE(ImplicitType);
        CASE(TypeReference);
        CASE(StructUnionMember);
        CASE(DotMemberClause);
        CASE(EmptyStatement);
        CASE(ElseClause);
        CASE(ConditionalStatement);
        CASE(DefaultCaseItem);
        CASE(PatternCaseItem);
        CASE(StandardCaseItem);
        CASE(CaseStatement);
        CASE(ForeverStatement);
        CASE(LoopStatement);
        CASE(DoWhileStatement);
        CASE(ReturnStatement);
        CASE(JumpStatement);
        CASE(TimingControlStatement);
        CASE(ProceduralAssignStatement);
        CASE(ProceduralForceStatement);
        CASE(ProceduralDeassignStatement);
        CASE(ProceduralReleaseStatement);
        CASE(DisableStatement);
        CASE(DisableForkStatement);
        CASE(NamedBlockClause);
        CASE(SequentialBlockStatement);
        CASE(NonblockingAssignmentStatement);
        CASE(BlockingAssignmentStatement);
        CASE(AddAssignmentStatement);
        CASE(SubtractAssignmentStatement);
        CASE(MultiplyAssignmentStatement);
        CASE(DivideAssignmentStatement);
        CASE(ModAssignmentStatement);
        CASE(AndAssignmentStatement);
        CASE(OrAssignmentStatement);
        CASE(XorAssignmentStatement);
        CASE(LogicalLeftShiftAssignmentStatement);
        CASE(LogicalRightShiftAssignmentStatement);
        CASE(ArithmeticLeftShiftAssignmentStatement);
        CASE(ArithmeticRightShiftAssignmentStatement);
        CASE(ImplicitNonAnsiPort);
        CASE(ExplicitNonAnsiPort);
        CASE(NonAnsiPortList);
        CASE(InterfacePortHeader);
        CASE(VariablePortHeader);
        CASE(SimpleNetPortType);
        CASE(InterconnectPortHeader);
        CASE(DataNetPortType);
        CASE(NetPortHeader);
        CASE(ImplicitAnsiPort);
        CASE(ExplicitAnsiPort);
        CASE(AnsiPortList);
        CASE(WildcardPortList);
        CASE(ParameterPortList);
        CASE(ModuleHeader);
        CASE(ModuleDeclaration);
        CASE(InterfaceHeader);
        CASE(InterfaceDeclaration);
        CASE(ProgramHeader);
        CASE(ProgramDeclaration);
        CASE(ExternModule);
        CASE(InitialBlock);
        CASE(FinalBlock);
        CASE(AlwaysBlock);
        CASE(AlwaysFFBlock);
        CASE(AlwaysCombBlock);
        CASE(AlwaysLatchBlock);
        CASE(GenerateBlock);
        CASE(DividerClause);
        CASE(TimeUnitsDeclaration);
        CASE(OrderedPortConnection);
        CASE(NamedPortConnection);
        CASE(WildcardPortConnection);
        CASE(HierarchicalInstance);
        CASE(HierarchyInstantiation);
        default: ASSERT(false && "Missing case");
    }
    return os;
#undef CASE
}

}