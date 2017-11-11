//------------------------------------------------------------------------------
// Statements.cpp
// Statement creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Statements.h"

#include "Expressions.h"

namespace slang {

const InvalidStatement InvalidStatement::Instance(nullptr);

void Statement::eval(EvalContext& context) const {
    switch (kind) {
        case StatementKind::Invalid: break;
        case StatementKind::List: as<StatementList>().eval(context); break;
        case StatementKind::SequentialBlock: as<SequentialBlockStatement>().eval(context); break;
        case StatementKind::ExpressionStatement: as<ExpressionStatement>().eval(context); break;
        case StatementKind::VariableDeclaration: as<VariableDeclStatement>().eval(context); break;
        case StatementKind::Return: as<ReturnStatement>().eval(context); break;
        case StatementKind::Conditional: as<ConditionalStatement>().eval(context); break;
        case StatementKind::ForLoop: as<ForLoopStatement>().eval(context); break;
    }
}

void StatementList::eval(EvalContext& context) const {
    for (auto item : list) {
        item->eval(context);
        if (context.hasReturned())
            break;
    }
}

void SequentialBlockStatement::eval(EvalContext& context) const {
    block.getBody().eval(context);
}

void ExpressionStatement::eval(EvalContext& context) const {
    expr.eval(context);
}

void VariableDeclStatement::eval(EvalContext& context) const {
    // Create storage for the variable
    ConstantValue initial;
    if (symbol.initializer())
        initial = symbol.initializer()->eval(context);

    context.createLocal(&symbol, initial);
}

void ReturnStatement::eval(EvalContext& context) const {
    // TODO: empty return?
    context.setReturned(expr->eval(context));
}

void ConditionalStatement::eval(EvalContext& context) const {
    if (cond.evalBool(context))
        ifTrue.eval(context);
    else if (ifFalse)
        ifFalse->eval(context);
}

void ForLoopStatement::eval(EvalContext& context) const {
    // TODO:
    /*for (auto initializer : loop.initializers)
    evaluateVariableDecl(*initializer);*/

    while (stopExpr.evalBool(context)) {
        statement.eval(context);
        for (auto step : steps)
            step->eval(context);
    }
}

}
