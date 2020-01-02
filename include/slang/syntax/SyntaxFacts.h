//------------------------------------------------------------------------------
// SyntaxFacts.cpp
// Various syntax-related utility methods.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

enum class SyntaxKind;
enum class TokenKind : uint16_t;

struct DataTypeSyntax;

class SyntaxFacts {
public:
    static SyntaxKind getUnaryPrefixExpression(TokenKind kind);
    static SyntaxKind getUnaryPostfixExpression(TokenKind kind);
    static SyntaxKind getLiteralExpression(TokenKind kind);
    static SyntaxKind getBinaryExpression(TokenKind kind);
    static SyntaxKind getKeywordNameExpression(TokenKind kind);
    static SyntaxKind getIntegerType(TokenKind kind);
    static SyntaxKind getKeywordType(TokenKind kind);
    static SyntaxKind getProceduralBlockKind(TokenKind kind);
    static SyntaxKind getModuleDeclarationKind(TokenKind kind);
    static SyntaxKind getModuleHeaderKind(TokenKind kind);
    static TokenKind getModuleEndKind(TokenKind kind);
    static TokenKind getDelimCloseKind(TokenKind kind);
    static TokenKind getSkipToKind(TokenKind kind);
    static int getPrecedence(SyntaxKind kind);
    static bool isSpecialMethodName(SyntaxKind kind);
    static bool isRightAssociative(SyntaxKind kind);
    static bool isPossibleDataType(TokenKind kind);
    static bool isPossibleExpression(TokenKind kind);
    static bool isPossibleStatement(TokenKind kind);
    static bool isNetType(TokenKind kind);
    static bool isPortDirection(TokenKind kind);
    static bool isPossibleArgument(TokenKind kind);
    static bool isOpenDelimOrKeyword(TokenKind kind);
    static bool isCloseDelimOrKeyword(TokenKind kind);
    static bool isComma(TokenKind kind);
    static bool isSemicolon(TokenKind kind);
    static bool isCloseBrace(TokenKind kind);
    static bool isIdentifierOrComma(TokenKind kind);
    static bool isPossibleExpressionOrComma(TokenKind kind);
    static bool isPossibleExpressionOrCommaOrDefault(TokenKind kind);
    static bool isPossibleExpressionOrTripleAnd(TokenKind kind);
    static bool isPossibleForInitializer(TokenKind kind);
    static bool isPossibleOpenRangeElement(TokenKind kind);
    static bool isPossiblePattern(TokenKind kind);
    static bool isPossibleDelayOrEventControl(TokenKind kind);
    static bool isEndKeyword(TokenKind kind);
    static bool isDeclarationModifier(TokenKind kind);
    static bool isMemberQualifier(TokenKind kind);
    static bool isDriveStrength(TokenKind kind);
    static bool isChargeStrength(TokenKind kind);
    static bool isEndOfParenList(TokenKind kind);
    static bool isEndOfBracedList(TokenKind kind);
    static bool isEndOfBracketedList(TokenKind kind);
    static bool isEndOfCaseItem(TokenKind kind);
    static bool isEndOfConditionalPredicate(TokenKind kind);
    static bool isEndOfAttribute(TokenKind kind);
    static bool isEndOfParameterList(TokenKind kind);
    static bool isEndOfTransSet(TokenKind kind);
    static bool isNotInType(TokenKind kind);
    static bool isNotInPortReference(TokenKind kind);
    static bool isNotInConcatenationExpr(TokenKind kind);
    static bool isNotInParameterList(TokenKind kind);
    static bool isPossiblePropertyPortItem(TokenKind kind);
    static bool isPossibleAnsiPort(TokenKind kind);
    static bool isPossibleNonAnsiPort(TokenKind kind);
    static bool isPossibleModportPort(TokenKind kind);
    static bool isPossibleFunctionPort(TokenKind kind);
    static bool isPossibleParameter(TokenKind kind);
    static bool isPossiblePortConnection(TokenKind kind);
    static bool isPossibleVectorDigit(TokenKind kind);
    static bool isPossibleLetPortItem(TokenKind kind);
    static bool isPossibleTransSet(TokenKind kind);
    static bool isBeforeOrSemicolon(TokenKind kind);
    static bool isMatchingDelims(TokenKind openKind, TokenKind closeKind);

    static string_view getSimpleTypeName(const DataTypeSyntax& syntax);

protected:
    SyntaxFacts() = default;
};

} // namespace slang