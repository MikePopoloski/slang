//------------------------------------------------------------------------------
//! @file SystemSubroutine.h
//! @brief System-defined subroutine handling
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/SemanticFacts.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/util/Util.h"

namespace slang::ast {

class EvalContext;
class Expression;
class Type;

/// @brief The base class for built-in system subroutines.
///
/// There is one instance of a derived class for each built-in
/// subroutine in the language. System subroutines must be
/// registered with the compilation in order to be findable
/// via name lookup.
class SLANG_EXPORT SystemSubroutine {
public:
    virtual ~SystemSubroutine() = default;

    using Args = std::span<const Expression* const>;

    /// The name of the subroutine (including the leading $).
    std::string name;

    /// The kind of subroutine (task or function).
    SubroutineKind kind;

    /// True if the subroutine has output (or ref / inout) args, and false otherwise.
    bool hasOutputArgs = false;

    /// Possible ways in which the subroutine may use a `with` clause.
    enum class WithClauseMode {
        /// The subroutine does not use a `with` clause.
        None,

        /// The subroutine is an iterator method.
        Iterator,

        /// The subroutine is a randomize method.
        Randomize
    };

    /// The way in which the subroutine may use a `with` clause.
    WithClauseMode withClauseMode = WithClauseMode::None;

    /// @returns true if the subroutine allows an empty argument to be
    /// passed for the given argument index.
    virtual bool allowEmptyArgument(size_t argIndex) const;

    /// @returns true if the subroutine allows a clocking event to be
    /// passed for the given argument index.
    virtual bool allowClockingArgument(size_t argIndex) const;

    /// @returns true if the given argument is unevaluated by the
    /// subroutine, and false otherwise.
    virtual bool isArgUnevaluated(size_t argIndex) const;

    /// Allows the subroutine to perform custom argument binding for the given
    /// argument index.
    virtual const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                           const syntax::ExpressionSyntax& syntax,
                                           const Args& previousArgs) const;

    /// @returns the effective width of the return value of the subroutine.
    ///
    /// This is used to reduce false-positive width conversion warnings for
    /// subroutines defined to return something like an `int` when in reality
    /// they can only ever return 1 or 0.
    virtual std::optional<bitwidth_t> getEffectiveWidth() const { return {}; }

    /// Allows the subroutine to perform checking of the arguments in a call expression.
    virtual const Type& checkArguments(const ASTContext& context, const Args& args,
                                       SourceRange range, const Expression* iterOrThis) const = 0;

    /// Performs constant evaluation of the subroutine, or reports an error if
    /// it's not allowed to be called in a constant context.
    virtual ConstantValue eval(EvalContext& context, const Args& args, SourceRange range,
                               const CallExpression::SystemCallInfo& callInfo) const = 0;

protected:
    /// Constructs a new system subroutine instance.
    SystemSubroutine(const std::string& name, SubroutineKind kind) : name(name), kind(kind) {}

    /// @returns a string that says "task" or "function" depending on the kind
    /// of subroutine this is.
    std::string_view kindStr() const;

    /// Reports an error for a bad argument expression.
    const Type& badArg(const ASTContext& context, const Expression& arg) const;

    /// Reports an error indicating that the subroutine is not allowed
    /// in a constant context.
    bool notConst(EvalContext& context, SourceRange range) const;

    /// Checks for and reports an error if a hierarhical name is used in
    /// the given expression.
    [[nodiscard]] bool noHierarchical(EvalContext& context, const Expression& expr) const;

    /// Checks that the number of provided arguments is allowed for the
    /// subroutine, and reports an appropriate error if not.
    bool checkArgCount(const ASTContext& context, bool isMethod, const Args& args,
                       SourceRange callRange, size_t min, size_t max) const;

    /// @returns a modified AST context that indicates it is in an unevaluated context.
    static ASTContext unevaluatedContext(const ASTContext& sourceContext);

    /// Helper method to register the given expression as an lvalue.
    static bool registerLValue(const Expression& expr, const ASTContext& context);
};

/// An implementation of the SystemSubroutine interface that has
/// basic argument types and a well-defined return type.
class SLANG_EXPORT SimpleSystemSubroutine : public SystemSubroutine {
public:
    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const syntax::ExpressionSyntax& syntax,
                                   const Args& previousArgs) const final;
    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* iterExpr) const final;

protected:
    SimpleSystemSubroutine(const std::string& name, SubroutineKind kind, size_t requiredArgs,
                           const std::vector<const Type*>& argTypes, const Type& returnType,
                           bool isMethod, bool isFirstArgLValue = false) :
        SystemSubroutine(name, kind), argTypes(argTypes), returnType(&returnType),
        requiredArgs(requiredArgs), isMethod(isMethod), isFirstArgLValue(isFirstArgLValue) {
        SLANG_ASSERT(requiredArgs <= argTypes.size());
    }

private:
    std::vector<const Type*> argTypes;
    const Type* returnType;
    size_t requiredArgs;
    bool isMethod;
    bool isFirstArgLValue;
};

/// An implementation of the SystemSubroutine interface that is also
/// a "simple" subroutine that is also not allowed in constant contexts.
class SLANG_EXPORT NonConstantFunction : public SimpleSystemSubroutine {
public:
    NonConstantFunction(const std::string& name, const Type& returnType, size_t requiredArgs = 0,
                        const std::vector<const Type*>& argTypes = {}, bool isMethod = false) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, requiredArgs, argTypes, returnType,
                               isMethod) {}

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

} // namespace slang::ast
