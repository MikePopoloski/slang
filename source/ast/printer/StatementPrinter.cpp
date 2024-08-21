//------------------------------------------------------------------------------
//! @file StatemenPrinter.
//! @brief Support for printing statements from the ast
//
// SPDX-FileCopyrightText: Michael Popoloski, Easics
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include <cctype>
#include <iostream>
#include <list>
#include <regex>
#include <set>
#include <string>
#include <string_view>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/HierarchicalReference.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/printer/defaultAstPrinter.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/ast/types/Type.h"
#include "slang/util/LanguageVersion.h"
#include "slang/util/Util.h"

namespace slang::ast {

/// A helper method that assists in printing an entire syntax tree back to source
/// text. A SyntaxPrinter with useful defaults is constructed, the tree is printed,
/// and the resulting text is returned.
// static std::string printFile(const SyntaxTree& treprints
void AstPrinter::handle(const InvalidStatement& t) {
    // wrap the invalid part of the code in a comment
    write("// InvalidStatement removed\n");
    visitDefault(t);
}

// wait_statement ::= wait ( expression ) statement_or_null
void AstPrinter::handle(const WaitStatement& t) {
    write("wait (");
    t.cond.visit(*this);
    write(")");
    t.stmt.visit(*this);
    write("\n");
}

// wait_statement ::= wait fork;
void AstPrinter::handle(const WaitForkStatement& t) {
    write("wait fork;\n");
}

// wait_statement ::= wait_order ( hierarchical_identifier { , hierarchical_identifier } )
// action_block
void AstPrinter::handle(const WaitOrderStatement& t) {
    write("wait_order (");
    for (auto hierarchical_identifier : t.events) {
        hierarchical_identifier->visit(*this);
        if (hierarchical_identifier != t.events.back()) {
            write(",");
        }
    }
    write(")");

    // action_block ::=statement _or_null | [ statement ] else statement
    t.ifTrue->visit(*this);
    if (t.ifFalse) {
        write("else");
        t.ifFalse->visit(*this);
    }
    write("\n");
}

// #test schrijven
void AstPrinter::handle(const EmptyStatement& t) {
    // Represents an empty statement, used as a placeholder or an anchor for attributes.
    writeAttributeInstances(t);
    write(";");
    // visitDefault(t);
}

// #test schrijven
void AstPrinter::handle(const StatementList& t) {
    // Represents a list of statements.
    visitDefault(t);
}

void AstPrinter::handle(const VariableDeclStatement& t) {
    t.symbol.visit(*this);
    write(";\n");
}

// disable_statement ::= disable fork ;
void AstPrinter::handle(const DisableForkStatement& t) {
    write("disable fork ;\n");
}

// disable_statement ::= disable hierarchical_block_identifier ;
void AstPrinter::handle(const DisableStatement& t) {
    write("disable");
    t.target.visit(*this);
    write(";\n");
}
// jump_statement ::=break ;
void AstPrinter::handle(const BreakStatement& t) {
    write("break;");
}

// jump_statement ::=continue ;
void AstPrinter::handle(const ContinueStatement& t) {
    write("continue;");
}

void AstPrinter::handle(const ExpressionStatement& t) {
    visitDefault(t);
    write(";\n");
}
// loop_statement ::= repeat ( expression ) statement_or_null
// statement_or_null ::=statement| { attribute_instance } ;
// statement ::= [ block_identifier : ] { attribute_instance } statement_item
void AstPrinter::handle(const RepeatLoopStatement& t) {
    write("repeat (");
    t.count.visit(*this);
    write(")");
    indentation_level++;
    t.body.visit(*this);
    indentation_level--;
    write("\n");
}
// loop_statement ::= forever statement_or_null
void AstPrinter::handle(const ForeverLoopStatement& t) {
    write("forever");
    indentation_level++;
    t.body.visit(*this);
    indentation_level--;
    write("\n");
}

// loop_statement ::= foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] )
// statement
void AstPrinter::handle(const ForeachLoopStatement& t) {
    write("foreach(");
    t.arrayRef.visit(*this);
    write("[");
    for (auto var : t.loopDims) {
        if (var.loopVar) {
            write(var.loopVar->name);
            if (var.loopVar != t.loopDims.back().loopVar)
                write(",");
        }
    }
    write("]");
    write(")");

    indentation_level++;
    t.body.visit(*this);
    indentation_level--;
    write("\n");
}
// loop_statement ::= while ( expression ) statement_or_null
void AstPrinter::handle(const WhileLoopStatement& t) {
    write("while (");
    t.cond.visit(*this);
    write(")");
    t.body.visit(*this);
    write("\n");
}
// for ( [ for_initialization ] ; [ expression ] ; [ for_step ] ) statement_or_null
void AstPrinter::handle(const ForLoopStatement& t) {
    write("for (");

    // for_initialization ::= list_of_variable_assignments
    for (auto initializer : t.initializers) {
        (*initializer).visit(*this);
        if (initializer != t.initializers.back()) {
            write(",");
        }
    }
    write(";");

    // stop expression
    t.stopExpr->visit(*this);
    write(";");

    // for_step_assignment ::=operator_assignment| inc_or_dec_expression |
    // function_subroutine_call
    for (auto step_expr : t.steps) {
        (*step_expr).visit(*this);
        if (step_expr != t.steps.back()) {
            write(",");
        }
    }
    write(")\n");
    indentation_level++;
    t.body.visit(*this);
    indentation_level--;
    write("\n");
}
// conditional_statement ::= [ unique_priority ] if ( cond_predicate ) statement_or_null {else
// if ( cond_predicate ) statement_or_null } [ else statement_or_null ]
void AstPrinter::handle(const ConditionalStatement& t) {

    if (t.check != UniquePriorityCheck::None) {
        std::string_view priority = toString(t.check);
        write(lowerFirstLetter(priority));
    }

    write("if(");
    // cond_predicate ::= expression_or_cond_pattern { &&& expression_or_cond_pattern }
    for (auto condition : t.conditions) {
        condition.expr.get()->visit(*this);
        // cond_pattern ::= expression matches pattern
        if (condition.pattern) {
            write("matches ");
            condition.pattern->visit(*this);
        }
        if (condition.expr.get() != t.conditions.back().expr.get()) {
            write("&&&");
        }
    }
    write(")\n");

    indentation_level++;
    t.ifTrue.visit(*this);
    indentation_level--;

    if (t.ifFalse) {
        write("else\n");
        indentation_level++;
        t.ifFalse->visit(*this);
        indentation_level--;
    }
}

// case_statement ::= [ unique_priority ] case_keyword ( case_expression ) case_item { case_item}
// endcase
//                  | [ unique_priority ] case ( case_expression ) inside case_inside_item {
//                  case_inside_item } endcase
void AstPrinter::handle(const CaseStatement& t) {
    if (t.check != UniquePriorityCheck::None) {
        std::string_view priority = toString(t.check);
        write(lowerFirstLetter(priority));
    }

    // case_keyword
    write(t.condition);
    write("(", false);
    t.expr.visit(*this);
    write(")", false);

    if (t.condition == CaseStatementCondition::Inside) {
        write("inside");
    }

    write("\n", false);

    indentation_level++;

    for (auto item : t.items) {
        // case_item :: case_item_expression { , case_item_expression } : statement_or_null
        for (auto expr : item.expressions) {
            expr->visit(*this);
            if (expr != item.expressions.back())
                write(",");
        }
        write(":");
        item.stmt->visit(*this);
        write("\n");
    }

    // case_item ::= | default [ : ] statement_or_null
    if (t.defaultCase) {
        write("default :");
        (*t.defaultCase).visit(*this);
        write("\n");
    }
    indentation_level--;

    write("endcase \n");
}



// #test schrijven
void AstPrinter::handle(const BlockStatement& t) {
    // edge case handeling
    // TODO BETERE MANER VINDEN
    // foreach creates a Blockstatement automaticly which causes a duplicate block statement
    // when trying to print the ast
    if (t.body.kind == StatementKind::ForeachLoop) {
        t.body.visit(*this);
        return;
    }
    // Represents a sequential or parallel block statement.
    if (t.blockKind == StatementBlockKind::Sequential) {
        write("begin");
    }
    else {
        write("fork");
    }

    if (t.blockSymbol) {
        write(":", false);
        write((*t.blockSymbol).name);
        write("\n");
    }
    else {
        write("\n");
    }

    indentation_level += 1;

    // first write the information from the statementBlock
    write(blockBuffer);
    blockBuffer = "";

    t.body.visit(*this);
    indentation_level -= 1;

    if (t.blockKind == StatementBlockKind::JoinAll) {
        write("join\n");
    }
    else if (t.blockKind == StatementBlockKind::JoinAny) {
        write("join_any\n");
    }
    else if (t.blockKind == StatementBlockKind::JoinNone) {
        write("join_none\n");
    }
    else {
        write("end\n");
    }
}

//immediate_assertion_statement        ::= simple_immediate_assertion_statement | deferred_immediate_assertion_statement
//simple_immediate_assertion_statement ::= simple_immediate_assert_statement
//simple_immediate_assert_statement    ::= assert ( expression ) action_block
//action_block ::=statement_or_null | [ statement ] else statement_or_null
void AstPrinter::handle(const ImmediateAssertionStatement& t){
    write(t.assertionKind);
    if(t.isDeferred)
        write(t.isFinal?"final":"#0");
    write("(");
    t.cond.visit(*this);
    write(")");
    if (t.ifTrue)
        t.ifTrue->visit(*this);

    if (t.ifFalse){
        write("else");
        t.ifFalse->visit(*this);
    }
}

} // namespace slang::ast
