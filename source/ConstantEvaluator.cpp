//------------------------------------------------------------------------------
// ConstantEvaluator.cpp
// Compile-time constant evaluation.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#include "ConstantEvaluator.h"

#include <algorithm>

#include "SemanticModel.h"

namespace slang {

ConstantEvaluator::ConstantEvaluator() {
    currentFrame = &rootFrame;
}

ConstantValue& ConstantEvaluator::createTemporary(const Symbol* key) {
    ConstantValue& result = currentFrame->temporaries[key];
    ASSERT(!result, "Created multiple temporaries with the same key");
    return result;
}

bool ConstantEvaluator::evaluateBool(const BoundNode* tree) {
    auto cv = evaluate(tree);
    if (!cv)
        return false;

    return (bool)(logic_t)cv.integer();
}

ConstantValue ConstantEvaluator::evaluate(const BoundNode* tree) {
    ASSERT(tree);
    if (tree->bad())
        return nullptr;

    switch (tree->kind) {
        case BoundNodeKind::Literal: return evaluateLiteral((BoundLiteral*)tree);
        case BoundNodeKind::Parameter: return evaluateParameter((BoundParameter*)tree);
        case BoundNodeKind::Variable: return evaluateVariable((BoundVariable*)tree);
        case BoundNodeKind::UnaryExpression: return evaluateUnary((BoundUnaryExpression*)tree);
        case BoundNodeKind::BinaryExpression: return evaluateBinary((BoundBinaryExpression*)tree);
        case BoundNodeKind::TernaryExpression: return evaluateConditional((BoundTernaryExpression*)tree);
        case BoundNodeKind::AssignmentExpression: return evaluateAssignment((BoundAssignmentExpression*)tree);
        case BoundNodeKind::CallExpression: return evaluateCall((BoundCallExpression*)tree);
        case BoundNodeKind::StatementList: return evaluateStatementList((BoundStatementList*)tree);
        case BoundNodeKind::ReturnStatement: return evaluateReturn((BoundReturnStatement*)tree);
        case BoundNodeKind::VariableDeclaration: return evaluateVariableDecl((BoundVariableDecl*)tree);

            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

ConstantValue ConstantEvaluator::evaluateLiteral(const BoundLiteral* expr) {
    return expr->value;
}

ConstantValue ConstantEvaluator::evaluateParameter(const BoundParameter* expr) {
    return expr->symbol.value;
}

ConstantValue ConstantEvaluator::evaluateVariable(const BoundVariable* expr) {
    ConstantValue& val = currentFrame->temporaries[expr->symbol];
    ASSERT(val);
    return val;
}

ConstantValue ConstantEvaluator::evaluateUnary(const BoundUnaryExpression* expr) {
    const auto v = evaluate(expr->operand).integer();

    switch (expr->syntax->kind) {
        case SyntaxKind::UnaryPlusExpression: return v;
        case SyntaxKind::UnaryMinusExpression: return -v;
        case SyntaxKind::UnaryBitwiseNotExpression: return ~v;
        case SyntaxKind::UnaryBitwiseAndExpression: return SVInt(v.reductionAnd());
        case SyntaxKind::UnaryBitwiseOrExpression: return SVInt(v.reductionOr());
        case SyntaxKind::UnaryBitwiseXorExpression: return SVInt(v.reductionXor());
        case SyntaxKind::UnaryBitwiseNandExpression: return SVInt(!v.reductionAnd());
        case SyntaxKind::UnaryBitwiseNorExpression: return SVInt(!v.reductionOr());
        case SyntaxKind::UnaryBitwiseXnorExpression: return SVInt(!v.reductionXor());
        case SyntaxKind::UnaryLogicalNotExpression: return SVInt(!v);
            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

ConstantValue ConstantEvaluator::evaluateBinary(const BoundBinaryExpression* expr) {
    const auto l = evaluate(expr->left).integer();
    const auto r = evaluate(expr->right).integer();

    switch (expr->syntax->kind) {
        case SyntaxKind::AddExpression: return l + r;
        case SyntaxKind::SubtractExpression: return l - r;
        case SyntaxKind::MultiplyExpression: return l * r;
        case SyntaxKind::DivideExpression: return l / r;
        case SyntaxKind::ModExpression: return l % r;
        case SyntaxKind::BinaryAndExpression: return l & r;
        case SyntaxKind::BinaryOrExpression: return l | r;
        case SyntaxKind::BinaryXorExpression: return l ^ r;
        case SyntaxKind::LogicalShiftLeftExpression: return l.shl(r);
        case SyntaxKind::LogicalShiftRightExpression: return l.lshr(r);
        case SyntaxKind::ArithmeticShiftLeftExpression: return l.shl(r);
        case SyntaxKind::ArithmeticShiftRightExpression: return l.ashr(r);
        case SyntaxKind::BinaryXnorExpression: return l.xnor(r);
        case SyntaxKind::EqualityExpression: return SVInt(l == r);
        case SyntaxKind::InequalityExpression: return SVInt(l != r);
        case SyntaxKind::CaseEqualityExpression: return SVInt((logic_t)exactlyEqual(l, r));
        case SyntaxKind::CaseInequalityExpression: return SVInt((logic_t)!exactlyEqual(l, r));
        case SyntaxKind::GreaterThanEqualExpression: return SVInt(l >= r);
        case SyntaxKind::GreaterThanExpression: return SVInt(l > r);
        case SyntaxKind::LessThanEqualExpression: return SVInt(l <= r);
        case SyntaxKind::LessThanExpression: return SVInt(l < r);
        case SyntaxKind::PowerExpression: return l.pow(r);
            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

ConstantValue ConstantEvaluator::evaluateConditional(const BoundTernaryExpression* expr) {
    const auto pred = (logic_t)evaluate(expr->pred).integer();

    if (pred.isUnknown()) {
        // do strange combination operation
        const auto l = evaluate(expr->left).integer();
        const auto r = evaluate(expr->right).integer();
        const auto k = l.ambiguousConditionalCombination(r);
        return k;
    } else if (bool(pred)) {
        // Only one side gets evaluate if true or false
        return evaluate(expr->left).integer();
    } else  {
        return evaluate(expr->right).integer();
    }

    return nullptr;
}

ConstantValue ConstantEvaluator::evaluateAssignment(const BoundAssignmentExpression* expr) {
    LValue lvalue;
    if (!evaluateLValue(expr->left, lvalue))
        return nullptr;

    auto rvalue = evaluate(expr->right);
    const SVInt l = evaluate(expr->left).integer();
    const SVInt r = rvalue.integer();

    switch (expr->syntax->kind) {
        case SyntaxKind::AssignmentExpression: lvalue.store(std::move(rvalue)); break;
        case SyntaxKind::AddAssignmentExpression: lvalue.store(l + r); break;
        case SyntaxKind::SubtractAssignmentExpression: lvalue.store(l - r); break;
        case SyntaxKind::MultiplyAssignmentExpression: lvalue.store(l * r); break;
        case SyntaxKind::DivideAssignmentExpression: lvalue.store(l / r); break;
        case SyntaxKind::ModAssignmentExpression: lvalue.store(l % r); break;
        case SyntaxKind::AndAssignmentExpression: lvalue.store(l & r); break;
        case SyntaxKind::OrAssignmentExpression: lvalue.store(l | r); break;
        case SyntaxKind::XorAssignmentExpression: lvalue.store(l ^ r); break;
        case SyntaxKind::LogicalLeftShiftAssignmentExpression: lvalue.store(l.shl(r)); break;
        case SyntaxKind::LogicalRightShiftAssignmentExpression: lvalue.store(l.lshr(r)); break;
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression: lvalue.store(l.shl(r)); break;
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression: lvalue.store(l.ashr(r)); break;
            DEFAULT_UNREACHABLE;
    }
    return lvalue.load();
}

ConstantValue ConstantEvaluator::evaluateCall(const BoundCallExpression* expr) {
    // If this is a system function we will just evaluate it directly
    auto subroutine = expr->subroutine;
    if (subroutine->systemFunction != SystemFunction::Unknown)
        return evaluateSystemCall(subroutine->systemFunction, expr->arguments);

    // Create a new frame that will become the head of the call stack.
    // Don't actually update that pointer until we finish evaluating arguments.
    Frame newFrame { currentFrame };

    for (uint32_t i = 0; i < subroutine->arguments.count(); i++)
        newFrame.temporaries[subroutine->arguments[i]] = evaluate(expr->arguments[i]);

    // Now update the call stack and evaluate the function body
    currentFrame = &newFrame;
    auto&& result = evaluate(subroutine->body);

    // Pop the frame and return the value
    currentFrame = newFrame.parent;
    return std::move(result);
}

ConstantValue ConstantEvaluator::evaluateSystemCall(SystemFunction func, ArrayRef<const BoundExpression*> arguments) {
    SmallVectorSized<ConstantValue, 8> args;
    for (auto arg : arguments)
        args.emplace(evaluate(arg));

    switch (func) {
        case SystemFunction::clog2: return SVInt(clog2(args[0].integer()));

            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

ConstantValue ConstantEvaluator::evaluateStatementList(const BoundStatementList* stmt) {
    ConstantValue result;
    for (auto item : stmt->list) {
        result = evaluate(item);
        if (item->kind == BoundNodeKind::ReturnStatement)
            break;
    }
    return result;
}

ConstantValue ConstantEvaluator::evaluateReturn(const BoundReturnStatement* stmt) {
    return evaluate(stmt->expr);
}

ConstantValue ConstantEvaluator::evaluateVariableDecl(const BoundVariableDecl* decl) {
    // Create storage for the variable
    auto& storage = createTemporary(decl->symbol);
    if (decl->symbol->initializer)
        storage = evaluate(decl->symbol->initializer);
    return nullptr;
}

bool ConstantEvaluator::evaluateLValue(const BoundExpression* expr, LValue& lvalue) {
    // lvalues have to be one of a few kinds of expressions
    switch (expr->kind) {
        case BoundNodeKind::Variable:
            lvalue.storage = &currentFrame->temporaries[((BoundVariable*)expr)->symbol];
            break;

            DEFAULT_UNREACHABLE;
    }
    return true;
}

}
