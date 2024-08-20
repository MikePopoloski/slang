//------------------------------------------------------------------------------
//! @file ExpressionPrinter.cpp
//! @brief adds Support for printing expressions from the ast
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

// #test schrijven
void AstPrinter::handle(const InvalidAssertionExpr& t) {
    // wrap the invalid part of the code in a comment
    // print instance
    if (t.child) {
        write("/* invalid code:");
        t.child->visit(*this);
        write("*/");
    }
}

// hierarchical_identifier ::= [ $root . ] { identifier constant_bit_select . } identifier
void AstPrinter::handle(const HierarchicalValueExpression& t) {
    // get path
    std::string path_name = "";
    t.symbol.getHierarchicalPath(path_name);
    write(path_name);
}

// net_lvalue ::={ net_lvalue { , net_lvalue } } (this is used in other instances asswel)
void AstPrinter::handle(const ConcatenationExpression& t) {
    write("{");
    for (auto op : t.operands()) {
        op->visit(*this);
        if (op != t.operands().back()) {
            write(",");
        }
    }
    write("}");
}

void AstPrinter::handle(const NewArrayExpression& t) {
    write("new");
    write("[");
    if (t.initExpr()) {
        (*t.initExpr()).visit(*this);
    }
    else {
        t.sizeExpr().visit(*this);
    }
    write("]");
}

// mintypmax_expression ::= expression | expression : expression : expression
void AstPrinter::handle(const MinTypMaxExpression& t) {
    t.min().visit(*this);
    write(":", false);
    t.typ().visit(*this);
    write(":", false);
    t.max().visit(*this);
}

// value_range ::= expression | [ expression : expression ]
// TODO uitzoeken waarvoor die valuerange kind dient
void AstPrinter::handle(const ValueRangeExpression& t) {
    write("[");
    t.left().visit(*this);
    write(":");
    t.right().visit(*this);
    write("]");
}

// blocking_assignment    ::= variable_lvalue = delay_or_event_control expression |
//                            variable_lvalue assignment_operator expression
// nonblocking_assignment ::= variable_lvalue <= [ delay_or_event_control ] expression
void AstPrinter::handle(const AssignmentExpression& t) {
    t.left().visit(*this);

    if (t.isCompound())
        write(t.op.value());

    if (t.isNonBlocking()) {
        write("<=", false);
    }
    else {
        write("=", false);
    }

    if (t.timingControl) {
        t.timingControl->visit(*this);
    }

    t.right().visit(*this);
}

void AstPrinter::handle(const UnaryExpression& t) {
    write(t.op);
    visitDefault(t);
}

void AstPrinter::handle(const BinaryExpression& t) {
    t.left().visit(*this);
    // ensures that compound operators work ex: += would be +=+ without this
    if (t.left().kind != ExpressionKind::LValueReference) {
        write(t.op);
    }
    t.right().visit(*this);
}

// subroutine_call_statement ::=subroutine_call ;
// subroutine_call ::= tf_call | system_tf_call | method_call | [ std:: ] randomize_call
//  ps_or_hierarchical_tf_identifier { attribute_instance } [ ( list_of_arguments ) ]
//  system_tf_call ::= system_tf_identifier [ ( list_of_arguments ) ]
void AstPrinter::handle(const CallExpression& t) {
    write(t.getSubroutineName());
    writeAttributeInstances(t);

    write("(");
    for (auto arg : t.arguments()) {
        arg->visit(*this);
        if (arg != t.arguments().back()) {
            write(",");
        }
    }
    write(")");
}

void AstPrinter::handle(const NamedValueExpression& t) {
    write(t.symbol.name);
}

// TODO DIT nakijken
void AstPrinter::handle(const UnbasedUnsizedIntegerLiteral& t) {
    logic_t l;

    if (t.getLiteralValue().isUnknown())
        write("'x");
    else if (t.getLiteralValue().value == slang::logic_t::Z_VALUE)
        write("'z");
    else {
        write("'");
        write(std::to_string(t.getLiteralValue().value));
    }
}

void AstPrinter::handle(const IntegerLiteral& t) {
    write(t.getValue().toString());
}

void AstPrinter::handle(const StringLiteral& t){
        write("\"");
        write(t.getValue(),false);
        write("\"",false);
}

void AstPrinter::handle(const ElementSelectExpression& t) {
    t.value().visit(*this);
    write("[", false);
    t.selector().visit(*this);
    write("]", false);
}


} // namespace slang::ast