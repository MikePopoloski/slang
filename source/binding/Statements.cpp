//------------------------------------------------------------------------------
// Statements.cpp
// Statement creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/Statements.h"

#include "slang/binding/Expressions.h"

namespace slang {

const InvalidStatement InvalidStatement::Instance(nullptr);
const StatementList StatementList::Empty({});

bool Statement::eval(EvalContext& context) const {
    switch (kind) {
        case StatementKind::Invalid: return false;
        case StatementKind::List: return as<StatementList>().eval(context);
        case StatementKind::SequentialBlock: return as<SequentialBlockStatement>().eval(context);
        case StatementKind::ExpressionStatement: return as<ExpressionStatement>().eval(context);
        case StatementKind::VariableDeclaration: return as<VariableDeclStatement>().eval(context);
        case StatementKind::Return: return as<ReturnStatement>().eval(context);
        case StatementKind::Conditional: return as<ConditionalStatement>().eval(context);
        case StatementKind::ForLoop: return as<ForLoopStatement>().eval(context);
    }
    THROW_UNREACHABLE;
}

bool StatementList::eval(EvalContext& context) const {
    for (auto item : list) {
        if (!item->eval(context))
            return false;
        if (context.hasReturned())
            break;
    }

    return true;
}

bool SequentialBlockStatement::eval(EvalContext& context) const {
    return block.getBody()->eval(context);
}

bool ExpressionStatement::eval(EvalContext& context) const {
    return bool(expr.eval(context));
}

bool VariableDeclStatement::eval(EvalContext& context) const {
    // Create storage for the variable
    ConstantValue initial;
    if (auto initializer = symbol.getInitializer()) {
        initial = initializer->eval(context);
        if (!initial)
            return false;
    }

    context.createLocal(&symbol, initial);
    return true;
}

bool ReturnStatement::eval(EvalContext& context) const {
    // TODO: empty return?
    context.setReturned(expr->eval(context));
    return true;
}

bool ConditionalStatement::eval(EvalContext& context) const {
    auto result = cond.eval(context);
    if (result.bad())
        return false;

    // TODO: non integers?
    if ((bool)(logic_t)result.integer())
        return ifTrue.eval(context);
    else if (ifFalse)
        return ifFalse->eval(context);
    return true;
}

bool ForLoopStatement::eval(EvalContext& context) const {
    if (!initializers.eval(context))
        return false;

    while (true) {
        if (stopExpr) {
            auto result = stopExpr->eval(context);
            if (result.bad())
                return false;

            // TODO: non integers?
            if (!(bool)(logic_t)result.integer())
                break;
        }

        if (!body.eval(context))
            return false;

        for (auto step : steps) {
            if (!step->eval(context))
                return false;
        }
    }
    return true;
}

}
