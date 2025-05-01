//------------------------------------------------------------------------------
//! @file SyntaxFacts.h
//! @brief Various syntax-related utility methods
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang::parsing {

enum class TokenKind : uint16_t;

}

namespace slang::syntax {

enum class SyntaxKind;

struct DataTypeSyntax;

/// A collection of static methods that query various facts related
/// to tokens and syntax nodes.
class SLANG_EXPORT SyntaxFacts {
public:
    using TokenKind = parsing::TokenKind;

    /// @return the kind of syntax that should be created for the given
    /// unary prefix operator token.
    static SyntaxKind getUnaryPrefixExpression(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// unary postfix operator token.
    static SyntaxKind getUnaryPostfixExpression(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// literal token.
    static SyntaxKind getLiteralExpression(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// binary operator token.
    static SyntaxKind getBinaryExpression(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// binary sequence operator token.
    static SyntaxKind getBinarySequenceExpr(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// binary property operator token.
    static SyntaxKind getBinaryPropertyExpr(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// name keyword token (like "this" or "super").
    static SyntaxKind getKeywordNameExpression(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// built-in integer keyword token.
    static SyntaxKind getIntegerType(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// built-in non-integer keyword token.
    static SyntaxKind getKeywordType(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// block token.
    static SyntaxKind getProceduralBlockKind(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// module / program / interface token.
    static SyntaxKind getModuleDeclarationKind(TokenKind kind);

    /// @return the kind of syntax that should be created for the given
    /// module / program / interface header token.
    static SyntaxKind getModuleHeaderKind(TokenKind kind);

    /// @return the corresponding end token for the opening
    /// module / program / interface token.
    static TokenKind getModuleEndKind(TokenKind kind);

    /// @return the corresponding closing delimiter for the given
    /// opening delimiter.
    static TokenKind getDelimCloseKind(TokenKind kind);

    /// @return the preferred token to skip to given the current token
    /// being observed (for skipping over invalid / error spans).
    static TokenKind getSkipToKind(TokenKind kind);

    /// @return the operator precedence for the given expression syntax kind.
    static int getPrecedence(SyntaxKind kind);

    /// @return true if the given syntax is a special method name
    /// (like built-in array manipulation methods).
    static bool isSpecialMethodName(SyntaxKind kind);

    /// @return true if the given expression kind is right associative.
    static bool isRightAssociative(SyntaxKind kind);

    /// @return true if the given token represents a possible data type expression.
    static bool isPossibleDataType(TokenKind kind);

    /// @return true if the given token represents a possible expression.
    static bool isPossibleExpression(TokenKind kind);

    /// @return true if the given token represents a possible statement.
    static bool isPossibleStatement(TokenKind kind);

    /// @return true if the given token represents a net type.
    static bool isNetType(TokenKind kind);

    /// @return true if the given token represents a port direction.
    static bool isPortDirection(TokenKind kind);

    /// @return true if the given token represents a possible argument.
    static bool isPossibleArgument(TokenKind kind);

    /// @return true if the given token represents a possible parameter assignment.
    static bool isPossibleParamAssignment(TokenKind kind);

    /// @return true if the given token represents an opening delimiter.
    static bool isOpenDelimOrKeyword(TokenKind kind);

    /// @return true if the given token represents a closing delimiter.
    static bool isCloseDelimOrKeyword(TokenKind kind);

    /// @return true if the given token represents a comma.
    static bool isComma(TokenKind kind);

    /// @return true if the given token represents a semicolon.
    static bool isSemicolon(TokenKind kind);

    /// @return true if the given token represents a closing brace.
    static bool isCloseBrace(TokenKind kind);

    /// @return true if the given token represents an identifier or a comma.
    static bool isIdentifierOrComma(TokenKind kind);

    /// @return true if the given token is not an identifier or a comma.
    static bool isNotIdOrComma(TokenKind kind);

    /// @return true if the given token represents a possible expression or a comma.
    static bool isPossibleExpressionOrComma(TokenKind kind);

    /// @return true if the given token represents a possible expression, comma, or "default"
    /// keyword.
    static bool isPossibleExpressionOrCommaOrDefault(TokenKind kind);

    /// @return true if the given token represents a possible expression or "&&&" token.
    static bool isPossibleExpressionOrTripleAnd(TokenKind kind);

    /// @return true if the given token represents a possible expression or an equals sign.
    static bool isPossibleExpressionOrEquals(TokenKind kind);

    /// @return true if the given token represents a possible for-statement variable initializer.
    static bool isPossibleForInitializer(TokenKind kind);

    /// @return true if the given token represents a possible value range element.
    static bool isPossibleValueRangeElement(TokenKind kind);

    /// @return true if the given token represents a possible conditional pattern.
    static bool isPossiblePattern(TokenKind kind);

    /// @return true if the given token represents a possible conditional pattern or a comma.
    static bool isPossiblePatternOrComma(TokenKind kind);

    /// @return true if the given token represents a possible delay or event control.
    static bool isPossibleDelayOrEventControl(TokenKind kind);

    /// @return true if the given token represents a possible instance.
    static bool isPossibleInstance(TokenKind kind);

    /// @return true if the given token represents a possible UDP body entry.
    static bool isPossibleUdpEntry(TokenKind kind);

    /// @return true if the given token represents a possible randsequence production rule.
    static bool isPossibleRsRule(TokenKind kind);

    /// @return true if the given token represents a possible struct member.
    static bool isPossibleStructMember(TokenKind kind);

    /// @return true if the given token is an ending keyword (like "endmodule", "endfunction", etc).
    static bool isEndKeyword(TokenKind kind);

    /// @return true if the given token is a declaration modifier (like "const" or "static").
    static bool isDeclarationModifier(TokenKind kind);

    /// @return true if the given token is a lifetime modifier (like "automatic" or "static").
    static bool isLifetimeModifier(TokenKind kind);

    /// @return true if the given token is a member qualifer (like "virtual" or "extern").
    static bool isMemberQualifier(TokenKind kind);

    /// @return true if the given token is a valid qualifier for a class method.
    static bool isMethodQualifier(TokenKind kind);

    /// @return true if the given token is a valid qualifier for a class property.
    static bool isPropertyQualifier(TokenKind kind);

    /// @return true if the given token is a valid qualifier for a constraint block.
    static bool isConstraintQualifier(TokenKind kind);

    /// @return true if the given token is a drive strength.
    static bool isDriveStrength(TokenKind kind);

    /// @return true if the given token is a charge strength.
    static bool isChargeStrength(TokenKind kind);

    /// @return true if the given token is a gate type.
    static bool isGateType(TokenKind kind);

    /// @return true if the given token represents the end of a parenthesized list.
    static bool isEndOfParenList(TokenKind kind);

    /// @return true if the given token represents the end of a braced list.
    static bool isEndOfBracedList(TokenKind kind);

    /// @return true if the given token represents the end of a bracketed list.
    static bool isEndOfBracketedList(TokenKind kind);

    /// @return true if the given token represents the end of a case item.
    static bool isEndOfCaseItem(TokenKind kind);

    /// @return true if the given token represents the end of a conditional predicate.
    static bool isEndOfConditionalPredicate(TokenKind kind);

    /// @return true if the given token represents the end of an attribute.
    static bool isEndOfAttribute(TokenKind kind);

    /// @return true if the given token represents the end of a parameter list.
    static bool isEndOfParameterList(TokenKind kind);

    /// @return true if the given token represents the end of a "trans" set.
    static bool isEndOfTransSet(TokenKind kind);

    /// @return true if the given token is not valid in a data type.
    static bool isNotInType(TokenKind kind);

    /// @return true if the given token is not valid in a port reference.
    static bool isNotInPortReference(TokenKind kind);

    /// @return true if the given token is not valid in a concatenation expression.
    static bool isNotInConcatenationExpr(TokenKind kind);

    /// @return true if the given token is not valid in a parameter list.
    static bool isNotInParameterList(TokenKind kind);

    /// @return true if the given token represents a possible property port item.
    static bool isPossiblePropertyPortItem(TokenKind kind);

    /// @return true if the given token represents a possible ansi port.
    static bool isPossibleAnsiPort(TokenKind kind);

    /// @return true if the given token represents a possible non-ansi port.
    static bool isPossibleNonAnsiPort(TokenKind kind);

    /// @return true if the given token represents a possible UDP port.
    static bool isPossibleUdpPort(TokenKind kind);

    /// @return true if the given token represents a possible modport port.
    static bool isPossibleModportPort(TokenKind kind);

    /// @return true if the given token represents a possible function port.
    static bool isPossibleFunctionPort(TokenKind kind);

    /// @return true if the given token represents a possible function parameter.
    static bool isPossibleParameter(TokenKind kind);

    /// @return true if the given token represents a port connection.
    static bool isPossiblePortConnection(TokenKind kind);

    /// @return true if the given token represents a possible vector digit.
    static bool isPossibleVectorDigit(TokenKind kind);

    /// @return true if the given token represents a "let" port item.
    static bool isPossibleLetPortItem(TokenKind kind);

    /// @return true if the given token represents a possible "trans" set.
    static bool isPossibleTransSet(TokenKind kind);

    /// @return true if the given token represents a possible timing check argument.
    static bool isPossibleTimingCheckArg(TokenKind kind);

    /// @return true if the given token represents a possible edge descriptor.
    static bool isPossibleEdgeDescriptor(TokenKind kind);

    /// @return true if the given token is the "before" keyword or a semicolon.
    static bool isBeforeOrSemicolon(TokenKind kind);

    /// @return true if the given tokens are matching open / close delimiters.
    static bool isMatchingDelims(TokenKind openKind, TokenKind closeKind);

    /// @return true if the given @a mod token is allowed after a token of kind @a prev
    static bool isModifierAllowedAfter(TokenKind mod, TokenKind prev);

    /// @return true if the given syntax node is allowed within a compilation unit.
    static bool isAllowedInCompilationUnit(SyntaxKind kind);

    /// @return true if the given syntax node is allowed within a generate block or region.
    static bool isAllowedInGenerate(SyntaxKind kind);

    /// @return true if the given syntax node is allowed within a module definition.
    static bool isAllowedInModule(SyntaxKind kind);

    /// @return true if the given syntax node is allowed within an interface definition.
    static bool isAllowedInInterface(SyntaxKind kind);

    /// @return true if the given syntax node is allowed within a program definition.
    static bool isAllowedInProgram(SyntaxKind kind);

    /// @return true if the given syntax node is allowed within an anonymous program definition.
    static bool isAllowedInAnonymousProgram(SyntaxKind kind);

    /// @return true if the given syntax node is allowed within a package definition.
    static bool isAllowedInPackage(SyntaxKind kind);

    /// @return true if the given syntax node is allowed within a clocking block.
    static bool isAllowedInClocking(SyntaxKind kind);

    /// @return true if the given syntax node is allowed within a checker declaration.
    static bool isAllowedInChecker(SyntaxKind kind);

    /// @return true if the given token kind is a drive strength for value '0'.
    static bool isStrength0(TokenKind kind);

    /// @return true if the given token kind is a drive strength for value '1'.
    static bool isStrength1(TokenKind kind);

    /// @return true if the given syntax kind is an assignment operator.
    static bool isAssignmentOperator(SyntaxKind kind);

    /// @return a string representing the name of the given data type, if it has a simple name.
    static std::string_view getSimpleTypeName(const DataTypeSyntax& syntax);

protected:
    SyntaxFacts() = default;
};

} // namespace slang::syntax
