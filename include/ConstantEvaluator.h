//------------------------------------------------------------------------------
// ConstantEvaluator.h
// Compile-time constant evaluation.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <map>
#include <optional>

#include "AllSyntax.h"
#include "BoundNodes.h"
#include "Diagnostics.h"

namespace slang {

class SemanticModel;
class Scope;

/// The ConstantEvaluator takes a bound tree and evaluates it to determine its
/// constant value. If the tree is not constant, appropriately diagnostics will
/// be emitted to allow the user to track down what went wrong.
class ConstantEvaluator {
public:
    ConstantEvaluator();

    /// Evaluates a bound tree, including all side effects. If this is not a
    /// constant expression diagnostics will issued to help indicate why not.
    ConstantValue evaluateExpr(const BoundExpression* tree);
    void evaluateStmt(const BoundStatement *tree);

    /// Evaluates a bound tree and then tries to interpret the result in
    /// a boolean context.
    bool evaluateBool(const BoundExpression* tree);

    /// Creates a temporary on the current stack frame. Call this before calling
    /// `evaluate` to material temporaries that don't have declarations within
    /// the evaluated tree.
    ConstantValue& createTemporary(const Symbol* key);

private:
    // Represents a single frame in the call stack.
    struct Frame {
        // A set of temporary values materialized within the stack frame.
        // Use a map so that the values don't move around in memory.
        std::map<const Symbol*, ConstantValue> temporaries;

        // A pointer to the frame that called into this frame.
        Frame* parent = nullptr;

        // Set to non-null when return has been issued in this frame
        ConstantValue returnValue;
        bool hasReturned = false;

        Frame() {}
        explicit Frame(Frame* parent) : parent(parent) {}
    };

    // Represents an lvalue; something that can appear on the left hand side
    // of an assignment expression. In general it means that it's some kind of
    // memory location that we can actually write to.
    struct LValue {
        ConstantValue* storage;

        // TODO: this is temporary until we support broader classes of lvalues
        void store(ConstantValue&& value) { (*storage) = std::move(value); }
        ConstantValue& load() { return (*storage); }
    };

    ConstantValue evaluateLiteral(const BoundLiteral* expr);
    ConstantValue evaluateParameter(const BoundParameter* expr);
    ConstantValue evaluateVariable(const BoundVariable* expr);
    ConstantValue evaluateUnary(const BoundUnaryExpression* expr);
    ConstantValue evaluateBinary(const BoundBinaryExpression* expr);
    ConstantValue evaluateConditional(const BoundTernaryExpression* expr);
    ConstantValue evaluateNary(const BoundNaryExpression* expr);
    ConstantValue evaluateSelect(const BoundSelectExpression* expr);
    ConstantValue evaluateAssignment(const BoundAssignmentExpression* expr);
    ConstantValue evaluateCall(const BoundCallExpression* expr);

    void evaluateStatementList(const BoundStatementList* stmt);
    void evaluateReturn(const BoundReturnStatement* stmt);
    void evaluateVariableDecl(const BoundVariableDecl* decl);
    void evaluateConditional(const BoundConditionalStatement* stmt);
    void evaluateForLoop(const BoundForLoopStatement *loop);

    ConstantValue evaluateSystemCall(SystemFunction func, ArrayRef<const BoundExpression*> arguments);

    bool evaluateLValue(const BoundExpression* expr, LValue& lvalue);

    // The root or bottom of the callstack.
    Frame rootFrame;

    // The current callstack frame.
    Frame* currentFrame;
};

}
