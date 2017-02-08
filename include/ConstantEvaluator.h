//------------------------------------------------------------------------------
// ConstantEvaluator.h
// Compile-time constant evaluation.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

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
    ConstantValue evaluate(const BoundNode* tree);

private:
    ConstantValue evaluateLiteral(const BoundLiteral* expr);
    ConstantValue evaluateParameter(const BoundParameter* expr);
    ConstantValue evaluateUnary(const BoundUnaryExpression* expr);
    ConstantValue evaluateBinary(const BoundBinaryExpression* expr);
};

}
