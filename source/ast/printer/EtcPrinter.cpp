//------------------------------------------------------------------------------
//! @file EtcPrinter.cpp
//! @brief adds Support for printing TimingControls, Types,... from the ast
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

// delay_control ::= # delay_value | # ( mintypmax_expression )
void AstPrinter::handle(const DelayControl& t) {
    write("#");
    if (t.expr.kind == ExpressionKind::MinTypMax) {
        write("(", false);
        t.expr.visit(*this);
        write(")", false);
    }
    else {
        t.expr.visit(*this);
    }
}

void AstPrinter::handle(const Delay3Control& t) {
    write("#");
    if (t.expr1.kind == ExpressionKind::MinTypMax) {
        // delay3 ::=  # ( mintypmax_expression [ , mintypmax_expression [ ,
        // mintypmax_expression ] ] )
        write("(", false);
        t.expr1.visit(*this);
        if (t.expr2) {
            write(",", false);
            (*t.expr2).visit(*this);

            if (t.expr3) {
                write(",", false);
                (*t.expr3).visit(*this);
            }
        }
        write(")", false);
    }
    else {
        // delay3 ::= # delay_value
        t.expr1.visit(*this);
    }
}

// event_control::= @ ( event_expression )
// event_expression ::=[ edge_identifier ] expression [ iff expression ]
void AstPrinter::handle(const SignalEventControl& t) {
    write("@(");
    if (t.edge == EdgeKind::BothEdges) {
        write("edge");
    }
    else {
        write(lower(toString(t.edge)));
    }
    t.expr.visit(*this);
    if (t.iffCondition) {
        write("iff");
        (*t.iffCondition).visit(*this);
    }
    write(")");
}

void AstPrinter::handle(const ImplicitEventControl& t) {
    write("@*");
}

// type_declaration ::= typedef data_type type_identifier { variable_dimension } ;
// TODO: formating type_str
void AstPrinter::handle(const TypeAliasType& t) {
    blockBuffer.append("typedef ");
    // ex: union tagged{void Invalid;int Valid;}m3.u$1 shoulden't have the m3.u$1
    std::string type_str = t.targetType.getType().toString();

    std::regex reg("}.*?(?= .\\S*?;)");
    type_str = std::regex_replace(type_str, reg, "}");

    int bracket_loc = type_str.rfind("}");
    blockBuffer.append(type_str.substr(0, bracket_loc + 1));
    blockBuffer.append(t.name);
    blockBuffer.append(";\n");

    // remove the name of the typealias to make it possible to compare them to getType() types
    int dot_loc = type_str.rfind(".");
    typeConversions.insert({type_str.substr(0, dot_loc), std::string(t.name)});
}

} // namespace slang::ast