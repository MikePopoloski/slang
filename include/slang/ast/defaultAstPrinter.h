//------------------------------------------------------------------------------
//! @file SyntaxPrinter.h
//! @brief Support for printing syntax nodes and tokens
//
// SPDX-FileCopyrightText: Michael Popoloski, Easics
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cctype>
#include <iostream>
#include <list>
#include <set>
#include <regex>
#include <string>
#include <string_view>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/HierarchicalReference.h"
#include "slang/ast/SemanticFacts.h"
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

/// Provides support for printing ast back to source code.
class AstPrinter : public ASTVisitor<AstPrinter, true, true, true> {
public:
    AstPrinter(slang::ast::Compilation& compilation) : compilation(compilation) {};

    /// Append raw text to the buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& append(std::string_view text);

    /// Print the provided @a trivia to the internal buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& print(parsing::Trivia trivia);

    /// Print the provided @a token to the internal buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& print(parsing::Token token);

    /// Print the provided @a node to the internal buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& print(const syntax::SyntaxNode& node);

    /// Print the provided @a tree to the internal buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& print(const syntax::SyntaxTree& tree);

    /// Sets whether to include trivia when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& setIncludeTrivia(bool include) {
        includeTrivia = include;
        return *this;
    }

    /// Sets whether to include preprocessor directives when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& setIncludeDirectives(bool include) {
        includeDirectives = include;
        return *this;
    }

    /// Sets whether to include preprocessor directives when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& setAnsiStyle(bool include) {
        includeDirectives = include;
        return *this;
    }

    /// @return a copy of the internal text buffer.
    std::string_view str() const { return buffer; }

    /// A helper method that assists in printing an entire syntax tree back to source
    /// text. A SyntaxPrinter with useful defaults is constructed, the tree is printed,
    /// and the resulting text is returned.
    // static std::string printFile(const SyntaxTree& treprints
    void handle(const InvalidStatement& t) {
        // wrap the invalid part of the code in a comment
        write("// InvalidStatement removed\n");
        visitDefault(t);
    }

    // wait_statement ::= wait ( expression ) statement_or_null
    void handle(const WaitStatement& t) {
        write("wait (");
        t.cond.visit(*this);
        write(")");
        t.stmt.visit(*this);
        write("\n");
    }

    // wait_statement ::= wait fork;
    void handle(const WaitForkStatement& t) { write("wait fork;\n"); }

    // wait_statement ::= wait_order ( hierarchical_identifier { , hierarchical_identifier } )
    // action_block
    void handle(const WaitOrderStatement& t) {
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
    void handle(const InvalidAssertionExpr& t) {
        // wrap the invalid part of the code in a comment
        // print instance
        if (t.child) {
            write("/* invalid code:");
            t.child->visit(*this);
            write("*/");
        }
    }

    // hierarchical_identifier ::= [ $root . ] { identifier constant_bit_select . } identifier
    void handle(const HierarchicalValueExpression& t) {
        // get path
        std::string path_name = "";
        t.symbol.getHierarchicalPath(path_name);
        write(path_name);
    }

    // net_lvalue ::={ net_lvalue { , net_lvalue } } (this is used in other instances asswel)
    void handle(const ConcatenationExpression& t) {
        write("{");
        for (auto op : t.operands()) {
            op->visit(*this);
            if (op != t.operands().back()) {
                write(",");
            }
        }
        write("}");
    }

    void handle(const NewArrayExpression& t){
        write("new");
        write("[");
        if (t.initExpr()){
            (*t.initExpr()).visit(*this);

        } else{
            t.sizeExpr().visit(*this);
        }
        write("]");
    }

    // mintypmax_expression ::= expression | expression : expression : expression
    void handle(const MinTypMaxExpression& t) {
        t.min().visit(*this);
        write(":", false);
        t.typ().visit(*this);
        write(":", false);
        t.max().visit(*this);
    }

    // value_range ::= expression | [ expression : expression ]
    // TODO uitzoeken waarvoor die valuerange kind dient
    void handle(const ValueRangeExpression& t) {
        write("[");
        t.left().visit(*this);
        write(":");
        t.right().visit(*this);
        write("]");
    }

    // blocking_assignment    ::= variable_lvalue = delay_or_event_control expression |
    //                            variable_lvalue assignment_operator expression
    // nonblocking_assignment ::= variable_lvalue <= [ delay_or_event_control ] expression
    void handle(const AssignmentExpression& t) {
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

    void handle(const UnaryExpression& t) {
        write(t.op);
        visitDefault(t);
    }

    void handle(const BinaryExpression& t) {
        t.left().visit(*this);
        // ensures that compound operators work ex: += would be +=+ without this
        if (t.left().kind != ExpressionKind::LValueReference) {
            write(t.op);
        }
        t.right().visit(*this);
    }

    //subroutine_call_statement ::=subroutine_call ;
    //subroutine_call ::= tf_call | system_tf_call | method_call | [ std:: ] randomize_call
    // ps_or_hierarchical_tf_identifier { attribute_instance } [ ( list_of_arguments ) ]
    // system_tf_call ::= system_tf_identifier [ ( list_of_arguments ) ]
    void handle(const CallExpression& t){
        write( t.getSubroutineName());
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

    void handle(const StringLiteral& t){
        write("\"");
        write(t.getValue(),false);
        write("\"",false);
    }


    // event_control::= @ ( event_expression )
    // event_expression ::=[ edge_identifier ] expression [ iff expression ]
    void handle(const SignalEventControl& t) {
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

    void handle(const ImplicitEventControl& t) { write("@*"); }

    // type_declaration ::= typedef data_type type_identifier { variable_dimension } ;
    // TODO: formating type_str
    void handle(const TypeAliasType& t) {
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
        typeConversions.insert({type_str.substr(0, dot_loc ), std::string(t.name)});
    }

    // #test schrijven
    void handle(const EmptyStatement& t) {
        // Represents an empty statement, used as a placeholder or an anchor for attributes.
        writeAttributeInstances(t);
        write(";");
        // visitDefault(t);
    }

    // #test schrijven
    void handle(const StatementList& t) {
        // Represents a list of statements.
        visitDefault(t);
    }

    void handle(const VariableDeclStatement& t) {
        t.symbol.visit(*this);
        write(";\n");
    }

    // disable_statement ::= disable fork ;
    void handle(const DisableForkStatement& t) { write("disable fork ;\n"); }

    // disable_statement ::= disable hierarchical_block_identifier ;
    void handle(const DisableStatement& t) {
        write("disable");
        t.target.visit(*this);
        write(";\n");
    }
    // jump_statement ::=break ;
    void handle(const BreakStatement& t) { write("break;"); }

    // jump_statement ::=continue ;
    void handle(const ContinueStatement& t) { write("continue;"); }

    void handle(const ExpressionStatement& t) {
        visitDefault(t);
        write(";");
    }
    // loop_statement ::= repeat ( expression ) statement_or_null
    // statement_or_null ::=statement| { attribute_instance } ;
    // statement ::= [ block_identifier : ] { attribute_instance } statement_item
    void handle(const RepeatLoopStatement& t) {
        write("repeat (");
        t.count.visit(*this);
        write(")");
        indentation_level++;
        t.body.visit(*this);
        indentation_level--;
        write("\n");
    }
    // loop_statement ::= forever statement_or_null
    void handle(const ForeverLoopStatement& t) {
        write("forever");
        indentation_level++;
        t.body.visit(*this);
        indentation_level--;
        write("\n");
    }

    // loop_statement ::= foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] )
    // statement
    void handle(const ForeachLoopStatement& t) {
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
    void handle(const WhileLoopStatement& t) {
        write("while (");
        t.cond.visit(*this);
        write(")");
        t.body.visit(*this);
        write("\n");
    }
    // for ( [ for_initialization ] ; [ expression ] ; [ for_step ] ) statement_or_null
    void handle(const ForLoopStatement& t) {
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
    void handle(const ConditionalStatement& t) {

        if (t.check != UniquePriorityCheck::None) {
            std::string_view priority = toString(t.check);
            write(lowerFirstLetter(priority));
        }

        write("if(");
        for (auto condition : t.conditions) {
            condition.expr.get()->visit(*this);
            if (condition.expr.get() != t.conditions.back().expr.get()) {
                write(",");
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

    // case_statement ::= [ unique_priority ] case_keyword ( case_expression ) case_item { case_item} endcase
    //                  | [ unique_priority ] case ( case_expression ) inside case_inside_item {   case_inside_item } endcase
    void handle(const CaseStatement& t) {
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

    // case_statement ::= | [ unique_priority ] case_keyword (case_expression )matches
    //                       case_pattern_item { case_pattern_item } endcase
    void handle(const PatternCaseStatement& t){
        if (t.check != UniquePriorityCheck::None) {
            std::string_view priority = toString(t.check);
            write(lowerFirstLetter(priority));
        }

        // case_keyword
        write(t.condition);
        write("(");
        t.expr.visit(*this);
        write(") matches\n");
        indentation_level++;

        //case_pattern_item ::= pattern [ &&& expression ] : statement_or_null
        for (auto item : t.items) {
            item.pattern.get()->visit(*this);
            if (item.filter){
                write("&&&");
                item.filter->visit(*this);
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

    // pattern ::= tagged member_identifier [ pattern ]
    void handle(const TaggedPattern& t){
        write("tagged");
        write(t.member.name);
        t.valuePattern->visit(*this);
    }

    // pattern ::=. variable_identifier
    void handle(const VariablePattern& t){
        write(".");
        write(t.variable.name,false);
    }
    // pattern ::= .*
    void handle(const WildcardPattern& t){
        write(".*");
    }

    //assignment_pattern ::= '{ expression { , expression } }
    void handle(const StructurePattern& t){
        write("'{");
        for (auto field_pattern : t.patterns){
            field_pattern.pattern->visit(*this);
            if (field_pattern.pattern != t.patterns.back().pattern)
                write(",");
        }
        write("}");
    }


    void handle(const StatementBlockSymbol& t) {
        // extra block  where variables, .. are defined that are used in the corresponding instance,
        // contains mostly redundant except TypeAliasTypes
        t.visit(makeVisitor([&](auto& visitor, const TypeAliasType& TypeAliasType) {
            handle(TypeAliasType);
            visitor.visitDefault(TypeAliasType);
        })); 
    }
    // #test schrijven
    void handle(const BlockStatement& t) {
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

    void handle(const PatternVarSymbol& t) {
        write(t.getType().toString(), true, true);
        write(t.name);
    }
    

    // attr_spec ::= attr_name [ = constant_expression ]
    // attr_name ::= identifier
    void handle(const AttributeSymbol& t) {
        write(t.name);
        if (auto value = t.getValue(); value) {
            write("=");
            write(value.toString());
        }
    }

    /*
    package_declaration ::=
            { attribute_instance } package [ lifetime ] package_identifier ;
            [ timeunits_declaration ] { { attribute_instance } package_item }
        endpackage [ : package_identifier ]
    */
    void handle(const PackageSymbol& t) {
        // attribute_instance ::= (* attr_spec { , attr_spec } *)
        writeAttributeInstances(t);

        write("package");

        write(t.defaultLifetime == VariableLifetime::Static ? "static" : "automatic");

        write(t.name);
        write(";\n", false);

        // I chose one type, info about the used declaration is not availble
        // timeunit time_literal [ / time_literal ] ;
        writeTimeUnitsDeclaration(t.timeScale);

        visitDefault(t);

        write("endpackage");
    }

    // anonymous_program ::= program ; { anonymous_program_item } endprogram
    void handle(const AnonymousProgramSymbol& t) {
        write("program;\n");
        visitDefault(t);
        write("endprogram");
    }

    // ding zoals initial
    void handle(const ProceduralBlockSymbol& t) {
        write(t.procedureKind);
        t.getBody().visit(*this);
    }

    // continuous_assign ::= assign [ drive_strength ] [ delay3 ] list_of_net_assignments ;
    //                     | assign [ delay_control ] list_of_variable_assignments ;
    void handle(const ContinuousAssignSymbol& t) {
        write("assign");
        // drive_strength ::= ( strength0 , strength1 )
        bool driveStrengthExists = t.getDriveStrength().first.has_value() &&
                                   t.getDriveStrength().second.has_value();
        if (driveStrengthExists) {
            write("(");
            write(lower(toString(t.getDriveStrength().first.value())), false);
            write("0", false);
            write(",", false);
            write(lower(toString(t.getDriveStrength().second.value())));
            write("1", false);
            write(")", false);
        }

        // delay3 | delay_control
        if (t.getDelay())
            t.getDelay()->visit(*this);

        // list_of_net_assignments | list_of_variable_assignments
        t.getAssignment().visit(*this);
    }

    // delay_control ::= # delay_value | # ( mintypmax_expression )
    void handle(const DelayControl& t) {
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

    void handle(const Delay3Control& t) {
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

    /// module_declaration    ::= module_ansi_header [ timeunits_declaration ] {
    /// non_port_module_item } endmodule [ : module_identifier ] interface_declaration ::=
    /// interface_ansi_header [ timeunits_declaration ] { non_port_interface_item } endinterface [ :
    /// interface_identifier ] program_declaration    ::= program_ansi_header [
    /// timeunits_declaration ] { non_port_program_item } endprogram [ : program_identifier ]

    /// module_ansi_header    ::= { attribute_instance } module_keyword [ lifetime ]
    /// module_identifier <{ package_import_declaration } [ parameter_port_list ] [
    /// list_of_port_declarations ];> interface_ansi_header ::= { attribute_instance } interface [
    /// lifetime ] interface_identifier <{ package_import_declaration } [ parameter_port_list ] [
    /// list_of_port_declarations ];> program_ansi_header   ::= { attribute_instance } program [
    /// lifetime ] program_identifier <{ package_import_declaration } [ parameter_port_list ] [
    /// list_of_port_declarations ] ;>
    /// <> is handeld in InstanceBodySymbol
    void handle(const slang::ast::InstanceSymbol& t) {
        // if it is already written somewhere else do not write it again
        if (initializedInstances.count(&(t.body)) != 0){
            return;
        }else {
            initializedInstances.insert(&(t.body));
        }

        writeAttributeInstances(t);

        // print instance
        std::string_view instanceSymbol = toString(t.getDefinition().definitionKind);
        std::string newSymbol = lowerFirstLetter(instanceSymbol);
        write(newSymbol);

        // write [ lifetime ] x_identifier
        t.getDefinition().visit(*this);

        // visit content instance <>
        t.body.visit(*this);

        // print endinstance
        write("end" + newSymbol + "\n");

        // check if there are connections that need to be made
        if (!t.getPortConnections().empty()) {
            // module_instantiation ::= module_identifier [ parameter_value_assignment ]
            // hierarchical_instance { , hierarchical_instance } ;
            write(t.body.name);
            // TODO parameter_value_assignment

            // hierarchical_instance ::= name_of_instance ( [ list_of_port_connections ] ) |
            // named_port_connection { , named_port_connection }
            write(t.name);
            write("(", false);
            // list_of_port_connections ::= named_port_connection { , named_port_connection } or
            // named equivalent
            for (auto named_port : t.getPortConnections()) {
                // named_port_connection ::= { attribute_instance } . port_identifier [ ( [
                // expression ] ) ]
                writeAttributeInstances(named_port->port);
                write(".");
                write(named_port->port.name, false);
                write("(", false);
                auto expression = named_port->getExpression();
                if (expression)
                    expression->visit(*this);
                write(")", false);

                if (named_port != t.getPortConnections().back())
                    write(",", false);
            }
            write(")", false);
        }
    }

    /// ansi_port_declaration ::=[ net_port_header  ] port_identifier { unpacked_dimension } [ =
    /// constant_expression ]
    ///                          | [ variable_port_header ] port_identifier { variable_dimension } [
    ///                          = constant_expression ]
    void handle(const slang::ast::PortSymbol& t) {
        // net_port_header      ::= [ port_direction ] net_port_type
        // variable_port_header ::= [ port_direction ] variable_port_type
        write(t.direction);

        if (t.internalSymbol) {
            t.internalSymbol->visit(*this);
        }
        else {
            write(convertType(t.getType().toString()), true, true);
        }
        // write port_identifier
        // write(t.name);
        if (!t.isNetPort()) {
            // variable_dimension ::= unsized_dimension | unpacked_dimension | associative_dimension
            // | queue_dimension
            // TODODODODODODOD samen met unpacked
        }

        if (t.getInternalExpr())
            t.getInternalExpr()->visit(*this);

        if (t.getInitializer()) {
            write("=", false);
            t.getInitializer()->visit(*this);
        }
    }

    /// ansi_port_declaration ::=[ interface_port_header ] port_identifier { unpacked_dimension } [
    /// = constant_expression ]
    void handle(const slang::ast::InterfacePortSymbol& t) {
        // interface_port_header ::= interface_identifier [ . modport_identifier]
        if (t.interfaceDef) {
            write(t.interfaceDef->name);
        }
        else {
            write("interface");
        }

        if (t.modport != "") {
            write(".", false);
            write(t.modport, false);
        }

        // write port_identifier
        write(t.name);

        // TODO:[ = constant_expression ]
    }

    /// net_port_type ::= [ net_type ] data_type_or_implicit
    void handle(const slang::ast::NetSymbol& t) {
        // TODO dewe lijst afwerken , betere manier vinder
        switch (t.netType.netKind) {
            case (NetType::NetKind::Wire):
                write("wire");
                break;
            case (NetType::NetKind::WAnd):
                write("wand");
                break;
            case (NetType::NetKind::WOr):
                write("wor");
                break;
            case (NetType::NetKind::Tri):
                write("tri");
                break;
            case (NetType::NetKind::TriAnd):
                write("triAnd");
                break;
            case (NetType::NetKind::TriOr):
                write("trior");
                break;
            case (NetType::NetKind::Tri0):
                write("tri0");
                break;
            case (NetType::NetKind::Tri1):
                write("tri1");
                break;
            case (NetType::NetKind::TriReg):
                write("trireg");
                break;
            case (NetType::NetKind::Supply0):
                write("supply0");
                break;
            case (NetType::NetKind::Supply1):
                write("supply1");
                break;
            case (NetType::NetKind::UWire):
                write("uwire");
                break;
            case (NetType::NetKind::Interconnect):
                write("interconnect");
                break;
        }

        write(convertType(convertType(t.getType().toString())), true, true);
        write(t.name);

        auto initializer = t.getInitializer();
        if (initializer) {
            write("=");
            initializer->visit(*this);
        }
    }

    void handle(const slang::ast::ScalarType& t) { write(t.name); }

    /// variable_port_type ::= var_data_type
    /// var_data_type      ::= data_type | var data_type_or_implicit
    // data_declaration10 ::=  [ var ] [ lifetime ] data_type_or_implicit
    void handle(const slang::ast::VariableSymbol& t) {
        write("var");
        write(t.lifetime == VariableLifetime::Static ? "static" : "automatic");
        write(convertType(t.getType().toString()), true, true);
        write(t.name);

        auto initializer = t.getInitializer();
        if (initializer) {
            write("=");
            initializer->visit(*this);
        }
    }

    void handle(const slang::ast::MultiPortSymbol& t) {
        if (t.isNullPort) {
            return visitDefault(t);
        }

        write(t.direction);

        write(convertType(t.getType().toString()), true, true);
        write(".");
        write(t.name, false);
        write("(\n", false);

        indentation_level++;
        for (auto port : t.ports) {
            if (!port)
                continue;

            port->visit(*this);

            if (port != t.ports.back())
                write(",\n", false);
        }
        indentation_level--;
        write(")");
    }

    /// parameter_declaration ::= parameter data_type_or_implicit list_of_param_assignments
    /// local_parameter_declaration ::= localparam data_type_or_implicit list_of_param_assignments
    /// list_of_param_assignments ::= param_assignment { , param_assignment }  always with lenght 1
    /// ?? param_assignment ::= parameter_identifier { unpacked_dimension } [ =
    /// constant_param_expression ]
    void handle(const slang::ast::ParameterSymbol& t) {
        // parameter|localparam
        if (t.isLocalParam()) {
            write(std::string_view("localparam"));
        }
        else {
            write(std::string_view("parameter"));
        }
        // data_type_or_implicit
        write(lowerFirstLetter(convertType(t.getType().toString())));
        // list_of_param_assignments->param_assignment->parameter_identifier
        write(t.name);
        // TODO:unpacked_dimension
        if (t.getInitializer())
            write("=", false);
        visitDefault(t);
    }

    // Represents a module, interface, or program definition
    void handle(const DefinitionSymbol& t) {
        write(t.defaultLifetime == VariableLifetime::Static ? "static" : "automatic");
        write(t.name);
    }

    /// package_import_item ::= package_identifier :: identifier
    void handle(const ExplicitImportSymbol& t) {
        write(t.packageName);
        write("::", false);
        write(t.importName);
    }

    // package_import_item ::= package_identifier :: *
    void handle(const WildcardImportSymbol& t) {
        write(t.packageName);
        write("::", false);
        write("*", false);
    }

    // modport_declaration ::= modport modport_item { , modport_item } ;
    // modport declartion with multiple items get automaticly splitted in multiple separete modport
    // declartions
    void handle(const ModportSymbol& t) {
        write("modport");
        // modport_item ::= modport_identifier ( modport_ports_declaration { ,
        // modport_ports_declaration } )
        write(t.name);
        write("(");
        visitDefault(t);
        write(")");
    }

    // net_alias ::= alias net_lvalue = net_lvalue { = net_lvalue } ;
    void handle(const NetAliasSymbol& t) {
        write("alias");
        for (auto expr : t.getNetReferences()) {
            expr->visit(*this);
            if (expr != t.getNetReferences().back())
                write("=");
        }
    }

    // modport_ports_declaration ::= { attribute_instance } modport_simple_ports_declaration
    // modport_simple_ports_declaration ::= port_direction modport_simple_port { ,
    // modport_simple_port}
    //
    void handle(const ModportPortSymbol& t) {
        writeAttributeInstances(t);
        write(t.direction);
        write(t.name);
    }

    void handle(const NamedValueExpression& t) { write(t.symbol.name); }

    /// { package_import_declaration } [ parameter_port_list ] [ list_of_port_declarations ];
    void handle(const InstanceBodySymbol& t) {
        indentation_level += 1;

        auto remainingMember = t.getFirstMember();

        // package_import_declaration ::= import package_import_item { , package_import_item } ;
        auto wildCard = t.getWildcardImportData();
        if (wildCard) {
            write("import");
            for (auto imports : wildCard->wildcardImports) {
                imports->visit(*this);
                if (imports != wildCard->wildcardImports.back())
                    write(",", false);
            }
            write(";", false);
        }

        // parameter_port_list ::= # ( list_of_param_assignments { , parameter_port_declaration } )
        if (!t.getParameters().empty()) {
            // TODO add Support for writing non ansi code
            write("#(", false);
            for (auto param : t.getParameters()) {
                if (!param)
                    continue;

                param->symbol.visit(*this);
                if (param != t.getParameters().back())
                    write(",", false);
            }
            remainingMember = ((Symbol*)t.getParameters().back())->getNextSibling();
            write(")");
        }

        // list_of_port_declarations2 ::=( [ { attribute_instance} ansi_port_declaration { , {
        // attribute_instance} ansi_port_declaration } ] )
        if (!t.getPortList().empty()) {
            write(std::string_view("(\n"), false);

            for (auto port : t.getPortList()) {
                if (!port)
                    continue;
                writeAttributeInstances(*port);

                port->visit(*this);
                if (port != t.getPortList().back())
                    write(",\n", false);
            }

            switch (t.getPortList().back()->kind) {
                case (SymbolKind::Port):
                    auto symbol = ((PortSymbol*)t.getPortList().back())->internalSymbol;
                    remainingMember = symbol ? symbol->getNextSibling() : t.getPortList().back();
                    break;
            }
            write(")");
        }

        write(";\n", false);

        // return if there are no remaining members
        while (remainingMember) {
            remainingMember->visit(*this);
            // TODO betere maniet voor dit vinden
            if ("\n" != buffer.substr(buffer.length() - 1, buffer.length() - 1)) {
                write(";\n", false);
            }

            remainingMember = remainingMember->getNextSibling();
        }
        // add a tab to all folowing code
        indentation_level -= 1;
    }

    //TODO DIT nakijken
    void handle(const UnbasedUnsizedIntegerLiteral& t){ 
        if (t.getLiteralValue().isUnknown())
            write("'x");
        else if(t.getLiteralValue() == logic_t::Z_VALUE)
            write("'z");
        else{
            write("'");
            write(std::to_string(t.getLiteralValue().value));
        }
    }
    void handle(const IntegerLiteral& t) { write(t.getValue().toString()); }

    void handle(const slang::ast::ElementSelectExpression& t) {
        t.value().visit(*this);
        write("[", false);
        t.selector().visit(*this);
        write("]", false);
    }

    std::string lowerFirstLetter(std::string_view string) {
        if (string == "")
            return "";
        // TODO: een beter manier vinden om dit te doen
        std::string new_string = std::string(string);
        new_string[0] = (char)tolower(new_string[0]);
        return new_string;
    }

    // lowers all letters of a string
    std::string lower(std::string_view string) {
        if (string == "")
            return "";
        // TODO: een beter manier vinden om dit te doen
        std::string new_string = std::string(string);
        for (auto& x : new_string) {
            x = tolower(x);
        }
        return new_string;
    }

private:
    std::string buffer;
    std::list<std::string> writeNextBuffer;
    std::set<const slang::ast::InstanceBodySymbol *> initializedInstances;
    // the type in the ast is not the type defined by the type alias, this map is used to convert the type back to the type alias type
    std::map<std::string, std::string> typeConversions;
    // buffer for code in a statementblock that needs to be appended in the next proceduralBlock
    std::string blockBuffer;
    Compilation& compilation;

    // variables that are declared in a statement block but not in the code
    // std::map<std::string_view,> variables;
    bool includeTrivia = true;
    bool includeMissing = false;
    bool includeSkipped = false;
    bool includeDirectives = false;
    bool includePreprocessed = true;
    bool includeComments = true;
    bool squashNewlines = true;

    // the amount of spaces after a newline is depth*depth_multplier
    int indentation_level = 0;
    const int indentation_multiplier = 3;

    // converts the type to a type defined by a type alias if a conversion is available
    std::string convertType(std::string type){
        // check if type in type conversions
        // remove the name of the typealias to make it possible to compare them to typealias types
        // ex: type alieas union tagged{void Invalid;int Valid;}m3.u$1 (this is named VInt)
        //     getType(): union tagged{void Invalid;int Valid;}m3.VInt
        std::regex reg("}.*?(?= .\\S*?;)");
        type = std::regex_replace(type, reg, "}");

        int dot_loc = type.rfind(".");
        if (typeConversions.count(type.substr(0, dot_loc )))
            return typeConversions[type.substr(0, dot_loc )];
        return type;

    }

    void write(std::string_view string, bool add_spacer = true, bool use_dollar = false) {
        // check if there is a $ sign in the string and add its content to the write next buffer
        // the $ is generated by the typewriter and repersents a jump ex: int$[] identifier -> int
        // identifier[]
        int dollarLocation = string.find("$");
        bool writeNextIsEmpty = writeNextBuffer.empty();
        if (dollarLocation != -1 && use_dollar) {
            std::string nextStr = std::string(string.substr(dollarLocation + 1));
            writeNextBuffer.push_back(nextStr);
            string = string.substr(0, dollarLocation);
        }

        if (buffer.back() == '\n') {
            // solves the indentation in new scopes
            std::string depth_string = std::string(indentation_level * indentation_multiplier, ' ');
            buffer.append(depth_string);
        }
        // buffer =="" is added to ensure the first char of the program does not have a space
        // infront of it
        else if (add_spacer && buffer != "") {
            buffer.append(" ");
        }
        buffer.append(std::string(string));

        if (!writeNextIsEmpty) {
            std::string element = writeNextBuffer.front();
            writeNextBuffer.pop_front();
            write(element, false);
        }
    }

    void writeAttributes(std::span<const AttributeSymbol* const> attributes) {
        if (!attributes.empty()) {
            write("(*");
            for (auto attrib : attributes) {
                attrib->visit(*this);
                if (attrib != attributes.back())
                    write(",", false);
                write("*) ");
            }
        }
    }

    void writeAttributeInstances(const Symbol& t) {
        auto attributes = compilation.getAttributes(t);
        writeAttributes(attributes);
    }

    void writeAttributeInstances(const Statement& t) {
        auto attributes = compilation.getAttributes(t);
        writeAttributes(attributes);
    }

    void writeAttributeInstances(const Expression& t) {
        auto attributes = compilation.getAttributes(t);
        writeAttributes(attributes);
    }

    void writeTimeUnitsDeclaration(const std::optional<TimeScale> t) {
        if (t.has_value()) {
            write("timeunit");
            write(t.value().toString());
            write(";");
        }
    }
    // TODO finish this list
    void write(BinaryOperator op) {
        switch (op) {
            case (BinaryOperator::Add):
                write("+", false);
                break;
            case (BinaryOperator::Subtract):
                write("-", false);
                break;
            case (BinaryOperator::Multiply):
                write("*", false);
                break;
            case (BinaryOperator::Equality):
                write("==", false);
                break;
            case (BinaryOperator::LessThan):
                write("<", false);
                break;
            case (BinaryOperator::LessThanEqual):
                write("<=", false);
                break;
            case (BinaryOperator::GreaterThan):
                write(">", false);
                break;
            case (BinaryOperator::GreaterThanEqual):
                write(">=", false);
                break;

            default:
                SLANG_UNREACHABLE;
        }
    }
    // TODO finish this list
    void write(UnaryOperator op) {
        switch (op) {
            case (UnaryOperator::Preincrement):
                write("++");
                break;
            case (UnaryOperator::Postincrement):
                write("$++", false, true);
                break;
            case (UnaryOperator::Predecrement):
                write("--");
                break;
            case (UnaryOperator::Postdecrement):
                write("$--", false, true);
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    void write(ArgumentDirection direction) {
        switch (direction) {
            case (ArgumentDirection::In):
                write("input", false);
                break;
            case (ArgumentDirection::Out):
                write("output", false);
                break;
            case (ArgumentDirection::InOut):
                write("inout", false);
                break;
            case (ArgumentDirection::Ref):
                write("ref", false);
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    void write(CaseStatementCondition caseName) {
        switch (caseName) {
            case (CaseStatementCondition::Inside):
            case (CaseStatementCondition::Normal):
                write("case");
                break;
            case (CaseStatementCondition::WildcardXOrZ):
                write("casex");
                break;
            case (CaseStatementCondition::WildcardJustZ):
                write("casez");
                break;

            default:
                SLANG_UNREACHABLE;
        }
    }

    void write(ProceduralBlockKind procedure) {
        switch (procedure) {
            case (ProceduralBlockKind::AlwaysComb):
                write("always_comb");
                break;
            case (ProceduralBlockKind::AlwaysLatch):
                write("always_latch");
                break;
            case (ProceduralBlockKind::AlwaysFF):
                write("always_ff");
                break;
            default:
                write(lowerFirstLetter(toString(procedure)));
        }
    }
};

} // namespace slang::ast
