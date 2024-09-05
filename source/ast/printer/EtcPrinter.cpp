//------------------------------------------------------------------------------
//! @file EtcPrinter.cpp
//! @brief adds Support for printing TimingControls, Types,... from the ast
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include <iterator>
#include "slang/ast/Constraints.h"
#include "slang/ast/printer/defaultAstPrinter.h"
#include "slang/util/Util.h"

namespace slang::ast {

void AstPrinter::handle(const EventListControl& t) {
    // These are only used in SignalEventControl. to make this syntax possible  @(A,B,....)
    this->inEventList = true;
    this->isFrontEventList = true;
    for (auto event : t.events) {
        if (event == t.events.back())
            this->isBackEventList = true;
        int currentBuffer = changedBuffer;
        event->visit(*this);
        this->isFrontEventList = false;

        if (event != t.events.back()&& changedBuffer != currentBuffer)
            write(",",false);
    }
    this->inEventList = false;
    this->isBackEventList = false;
    this->inEventList = false;

    
}

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
    if (isFrontEventList || !inEventList)
        write("@(");

    if (t.edge == EdgeKind::BothEdges) {
        write("edge");
    }
    else if (t.edge!=EdgeKind::None){
        write(lower(toString(t.edge)));
    }

    t.expr.visit(*this);

    if (t.iffCondition) {
        write("iff");
        (*t.iffCondition).visit(*this);
    }
    if (isBackEventList || !inEventList)
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
/*
class_declaration ::=
[ virtual ] class [ lifetime ] class_identifier [ parameter_port_list ]
[ extends class_type [ ( list_of_arguments ) ] ]
[ implements interface_class_type { , interface_class_type } ] ;
{ class_item }
endclass [ : class_identifier]*/
void AstPrinter::handle(const ClassType& t) {
    if (t.isAbstract)
        write("virtual");
    write("class");

    if (t.thisVar){
        // [ lifetime ] class_identifier
        write(t.thisVar->lifetime == VariableLifetime::Static ? "static" : "automatic");
        const Type& data_type = t.thisVar->getDeclaredType().get()->getType();
        write(convertType(data_type.toString()), true, true);
    }

    if (t.getBaseClass() != nullptr){
        write("extends");
        write(t.getBaseClass()->name);
    }

    if (!t.getDeclaredInterfaces().empty()){
        write("implements");
        for (auto interface: t.getDeclaredInterfaces()){
            interface->visit(*this);
        }
    }
    write(";\n");

    indentation_level++;
    visitMembers(t.getFirstMember() ,";");
    indentation_level--;

    write("endclass\n");
}

//covergroup_declaration ::=covergroup covergroup_identifier [ ( [ tf_port_list ] ) ] [ coverage_event ] ;{ coverage_spec_or_option } endgroup [ : covergroup_identifier ]
void AstPrinter::handle(const CovergroupType& t) {
    write("covergroup");
    write(t.name);
    // ( [ tf_port_list ] )
    if(!t.getArguments().empty()){
        write("(");
        visitMembers(t.getArguments());
        write(")");
    }

    if (t.getCoverageEvent())
        t.getCoverageEvent()->visit(*this);
    
    write(";\n");
    
    visitMembers(t.getArguments().back()->getNextSibling(),";");
    
    write("endgroup\n");
}

// coverage_option ::= option.member_identifier = expression
//                      type_option.member_identifier = constant_expression
void AstPrinter::handle(const CoverageOptionSetter& t){
    t.getExpression().visit(*this);
}

                 
void AstPrinter::handle(const ConstraintList& t) {
    visitMembers<Constraint>(t.list, ";",true);
}

void AstPrinter::handle(const ExpressionConstraint& t) {
    if(t.isSoft)
        write("soft");
    t.expr.visit(*this);
}

//constraint_expression ::=[ soft ] expression –> constraint_set ;
void AstPrinter::handle(const ImplicationConstraint& t) {
    //t.expr.visit(*this);
    t.predicate.visit(*this);
    write("->");
    write("{");
    t.body.visit(*this);
    write(";");
    write("}\n");

}

//constraint_block_item ::= solve solve_before_list before solve_before_list ;
void AstPrinter::handle(const SolveBeforeConstraint& t) {
    write("solve");
    visitMembers<>(t.solve);
    write("before");
    visitMembers<>(t.after);

    //t.expr.visit(*this);
}

//
void AstPrinter::handle(const ConditionalConstraint& t) {
    write("if(");
    t.predicate.visit(*this);
    write("){\n");

    indentation_level++;
    t.ifBody.visit(*this);
    indentation_level--;

    write("}\n");
    if (t.elseBody){
        write("else{\n");
        t.elseBody->visit(*this);
    }
    write("}\n");
    }

void AstPrinter::handle(const DisableSoftConstraint& t) {
    write("disable soft");
    t.target.visit(*this);
}
// t.expr.visit(*this);

//constraint_expression ::= foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] ) constraint_set
void AstPrinter::handle(const slang::ast::ForeachConstraint& t) {
    write("foreach(" );
    t.arrayRef.visit(*this);
    if (!t.loopDims.empty()){
        write("[",false);
        for(auto LoopDim:t.loopDims ){
            writeName(*LoopDim.loopVar);
            if (LoopDim.range.has_value())
                write(LoopDim.range.value().toString(),false);

        }
        write("]",false);
    }
    write(")",false );
    write("{\n",false);
    indentation_level++;
    t.body.visit(*this);
    indentation_level--;
    write("}\n",false);
}

}
 // namespace slang::ast