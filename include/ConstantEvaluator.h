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
    ConstantValue evaluate(const BoundNode* tree);

    /// Evaluates a bound tree and then tries to interpret the result in
    /// a boolean context.
    bool evaluateBool(const BoundNode* tree);

    /// Creates a temporary on the root stack frame. Call this before calling
    /// `evaluate` to material temporaries that don't have declarations within
    /// the evaluated tree.
    ConstantValue& createTemporary(const Symbol* key);

private:
    // Represents a single frame in the call stack.
    struct Frame {
        // A set of temporary values materialized within the stack frame.
        // Use a map so that the values don't move around in memory.
        std::map<const Symbol*, ConstantValue> temporaries;
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
    ConstantValue evaluateVarRef(const BoundVarRef* expr);
    ConstantValue evaluateUnary(const BoundUnaryExpression* expr);
    ConstantValue evaluateBinary(const BoundBinaryExpression* expr);
    ConstantValue evaluateAssignment(const BoundAssignmentExpression* expr);
    bool evaluateLValue(const BoundExpression* expr, LValue& lvalue);

    // The root or bottom of the callstack.
    Frame rootFrame;

    // The current callstack frame.
    Frame* currentFrame;
};

}
