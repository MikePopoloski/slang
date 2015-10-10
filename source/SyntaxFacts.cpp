#include <cstdint>
#include <memory>
#include <string>
#include <algorithm>

#include "BumpAllocator.h"
#include "StringRef.h"
#include "Token.h"
#include "SyntaxNode.h"

namespace slang {

SyntaxKind getUnaryExpression(TokenKind kind) {
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

SyntaxKind getLiteralExpression(TokenKind kind) {
    switch (kind) {
        case TokenKind::StringLiteral: return SyntaxKind::StringLiteralExpression;
        case TokenKind::IntegerLiteral: return SyntaxKind::IntegerLiteralExpression;
        case TokenKind::RealLiteral: return SyntaxKind::RealLiteralExpression;
        case TokenKind::TimeLiteral: return SyntaxKind::TimeLiteralExpression;
        case TokenKind::NullKeyword: return SyntaxKind::NullLiteralExpression;
        case TokenKind::Dollar: return SyntaxKind::WildcardLiteralExpression;
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
        default: return SyntaxKind::Unknown;
    }
}

SyntaxKind getAssignmentExpression(TokenKind kind) {
    switch (kind) {
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
        case TokenKind::SuperKeyword: return SyntaxKind::SuperHandle;
        case TokenKind::ThisKeyword: return SyntaxKind::ThisHandle;
        default: return SyntaxKind::Unknown;
    }
}

int getPrecedence(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            return 1;
        case SyntaxKind::LogicalOrExpression:
            return 2;
        case SyntaxKind::LogicalAndExpression:
            return 3;
        case SyntaxKind::BinaryOrExpression:
            return 4;
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
            return 5;
        case SyntaxKind::BinaryAndExpression:
            return 6;
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
        case SyntaxKind::CaseEqualityExpression:
        case SyntaxKind::CaseInequalityExpression:
        case SyntaxKind::WildcardEqualityExpression:
        case SyntaxKind::WildcardInequalityExpression:
            return 7;
        case SyntaxKind::LessThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::GreaterThanEqualExpression:
            return 8;
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
            return 9;
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
            return 10;
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::DivideExpression:
        case SyntaxKind::ModExpression:
            return 11;
        case SyntaxKind::PowerExpression:
            return 12;
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
            return 13;
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
        CASE(OrderedParameterAssignment);
        CASE(NamedParameterAssignment);
        CASE(ParameterValueAssignment);
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
        CASE(ParenthesizedExpression);
        CASE(MinTypMaxExpression);
        CASE(EmptyQueueExpression);
        CASE(ConcatenationExpression);
        CASE(MultipleConcatenationExpression);
        CASE(StreamingConcatenationExpression);
        CASE(StreamExpression);
        CASE(StreamExpressionWithRange);
        CASE(BitSelect);
        CASE(SimpleRangeSelect);
        CASE(AscendingRangeSelect);
        CASE(DescendingRangeSelect);
        CASE(ElementSelectExpression);
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
        CASE(ClassOrPackageScope);
        CASE(RootScope);
        CASE(IdentifierName);
        CASE(ClassName);
        CASE(HierarchicalName);
        CASE(SystemName);
        CASE(ThisHandle);
        CASE(SuperHandle);
    }
    return os;
#undef CASE
}

}