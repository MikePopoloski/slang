//------------------------------------------------------------------------------
//! @file CallExpression.h
//! @brief Definitions for call expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Constraints.h"
#include "slang/ast/Expression.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class FormalArgumentSymbol;

/// Represents a subroutine call.
class SLANG_EXPORT CallExpression : public Expression {
public:
    /// Extra information associated with an iterator method call.
    struct IteratorCallInfo {
        /// The iterator expression specified with the call.
        const Expression* iterExpr = nullptr;

        /// The iterator variable.
        const ValueSymbol* iterVar = nullptr;
    };

    /// Extra information associated with a randomize method call.
    struct RandomizeCallInfo {
        /// Inline constraints specified with the call, if any.
        const Constraint* inlineConstraints = nullptr;

        /// Extra constraint restrictions that apply, if any.
        std::span<const std::string_view> constraintRestrictions;
    };

    /// Additional context that applies to system subroutine calls.
    struct SystemCallInfo {
        /// The system subroutine being called.
        not_null<const SystemSubroutine*> subroutine;

        /// The scope in which the call occurs.
        not_null<const Scope*> scope;

        /// Additional information that applies to the call.
        std::variant<std::monostate, IteratorCallInfo, RandomizeCallInfo> extraInfo;

        /// @returns the extra info if this is for an iterator call, and
        /// an empty pair of nullptr if not.
        std::pair<const Expression*, const ValueSymbol*> getIteratorInfo() const;
    };

    using Subroutine = std::variant<const SubroutineSymbol*, SystemCallInfo>;

    /// The subroutine that is being called.
    Subroutine subroutine;

    CallExpression(const Subroutine& subroutine, const Type& returnType,
                   const Expression* thisClass, std::span<const Expression*> arguments,
                   LookupLocation lookupLocation, SourceRange sourceRange) :
        Expression(ExpressionKind::Call, returnType, sourceRange), subroutine(subroutine),
        thisClass_(thisClass), arguments_(arguments), lookupLocation(lookupLocation) {}

    /// If this call is for a class method, returns the expression representing the
    /// class handle on which the method is being invoked. Otherwise returns nullptr.
    const Expression* thisClass() const { return thisClass_; }

    /// @returns the arguments to the call.
    std::span<const Expression* const> arguments() const { return arguments_; }

    /// @returns the arguments to the call.
    std::span<const Expression*> arguments() { return arguments_; }

    /// @returns true if this is a call of a system subroutine.
    bool isSystemCall() const { return subroutine.index() == 1; }

    /// @returns the name of the subroutine being called.
    std::string_view getSubroutineName() const;

    /// @returns the kind of subroutine being called.
    SubroutineKind getSubroutineKind() const;

    /// @returns true if the called subroutine has output (or inout / ref) arguments.
    bool hasOutputArgs() const;

    ConstantValue evalImpl(EvalContext& context) const;
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;
    EffectiveSign getEffectiveSignImpl(bool isForConversion) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::InvocationExpressionSyntax& syntax,
                                  const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                  const ASTContext& context);

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::ArrayOrRandomizeMethodExpressionSyntax& syntax,
                                  const ASTContext& context);

    static Expression& fromLookup(Compilation& compilation, const Subroutine& subroutine,
                                  const Expression* thisClass,
                                  const syntax::InvocationExpressionSyntax* syntax,
                                  const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                  SourceRange range, const ASTContext& context);

    static Expression& fromArgs(Compilation& compilation, const Subroutine& subroutine,
                                const Expression* thisClass,
                                const syntax::ArgumentListSyntax* argSyntax, SourceRange range,
                                const ASTContext& context);

    static Expression& fromSystemMethod(
        Compilation& compilation, const Expression& expr,
        const LookupResult::MemberSelector& selector,
        const syntax::InvocationExpressionSyntax* syntax,
        const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause,
        const ASTContext& context);

    static Expression* fromBuiltInMethod(
        Compilation& compilation, SymbolKind rootKind, const Expression& expr,
        std::string_view methodName, const syntax::InvocationExpressionSyntax* syntax,
        const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause,
        const ASTContext& context);

    static bool bindArgs(const syntax::ArgumentListSyntax* argSyntax,
                         std::span<const FormalArgumentSymbol* const> formalArgs,
                         std::string_view symbolName, SourceRange range, const ASTContext& context,
                         SmallVectorBase<const Expression*>& boundArgs, bool isBuiltInMethod);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Call; }

    template<typename TVisitor>
    void visitExprsNoArgs(TVisitor&& visitor) const {
        if (thisClass())
            thisClass()->visit(visitor);

        if (isSystemCall()) {
            auto& extra = std::get<1>(subroutine).extraInfo;
            if (extra.index() == 1) {
                if (auto iterExpr = std::get<1>(extra).iterExpr)
                    iterExpr->visit(visitor);
            }
            else if (extra.index() == 2) {
                if (auto constraints = std::get<2>(extra).inlineConstraints)
                    constraints->visit(visitor);
            }
        }
    }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        visitExprsNoArgs(visitor);
        for (auto arg : arguments())
            arg->visit(visitor);
    }

private:
    static Expression& fromSyntaxImpl(
        Compilation& compilation, const ExpressionSyntax& left,
        const syntax::InvocationExpressionSyntax* invocation,
        const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause,
        const ASTContext& context);

    static Expression& createSystemCall(
        Compilation& compilation, const SystemSubroutine& subroutine, const Expression* firstArg,
        const syntax::InvocationExpressionSyntax* syntax,
        const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause, SourceRange range,
        const ASTContext& context, const Scope* randomizeScope = nullptr);

    static bool checkConstant(EvalContext& context, const SubroutineSymbol& subroutine,
                              SourceRange range);

    const Expression* thisClass_;
    std::span<const Expression*> arguments_;
    LookupLocation lookupLocation;
};

} // namespace slang::ast
