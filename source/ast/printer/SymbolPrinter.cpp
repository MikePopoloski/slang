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
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/printer/defaultAstPrinter.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/ast/types/Type.h"
#include "slang/util/LanguageVersion.h"
#include "slang/util/Util.h"

namespace slang::ast {

// genvar_initialization ::= [ genvar ] genvar_identifier = constant_expression
void AstPrinter::handle(const GenvarSymbol& t) {
    write("genvar");
    write(t.name);
}

// attr_spec ::= attr_name [ = constant_expression ]
// attr_name ::= identifier
void AstPrinter::handle(const AttributeSymbol& t) {
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
void AstPrinter::handle(const PackageSymbol& t) {
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
void AstPrinter::handle(const AnonymousProgramSymbol& t) {
    write("program;\n");
    visitDefault(t);
    write("endprogram");
}

// ding zoals initial
void AstPrinter::handle(const ProceduralBlockSymbol& t) {
    write(t.procedureKind);

    t.getBody().visit(*this);
}

// continuous_assign ::= assign [ drive_strength ] [ delay3 ] list_of_net_assignments ;
//                     | assign [ delay_control ] list_of_variable_assignments ;
void AstPrinter::handle(const ContinuousAssignSymbol& t) {
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
void AstPrinter::handle(const slang::ast::InstanceSymbol& t) {
    writeAttributeInstances(t);

    // print instance
    std::string_view instanceSymbol = toString(t.getDefinition().definitionKind);
    std::string newSymbol = lowerFirstLetter(instanceSymbol);
    write(newSymbol);

    // write [ lifetime ] x_identifier
    t.getDefinition().visit(*this);

    // visit content instance <>
    indentation_level += 1;
    t.body.visit(*this);
    indentation_level -= 1;

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
        write(");\n", false);
    }
}

/// ansi_port_declaration ::=[ net_port_header  ] port_identifier { unpacked_dimension } [ =
/// constant_expression ]
///                          | [ variable_port_header ] port_identifier { variable_dimension } [=
///                          constant_expression ]
void AstPrinter::handle(const slang::ast::PortSymbol& t) {
    // net_port_header      ::= [ port_direction ] net_port_type
    // variable_port_header ::= [ port_direction ] variable_port_type
    write(t.direction);

    if (t.internalSymbol) {
        t.internalSymbol->visit(*this);
        internalSymbols.insert(t.internalSymbol);
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
void AstPrinter::handle(const slang::ast::InterfacePortSymbol& t) {
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
void AstPrinter::handle(const slang::ast::NetSymbol& t) {
    if (!t.isImplicit) {
        write(t.netType.netKind);
        write(convertType(t.getType().toString()), true, true);
    }
    write(t.name);

    auto initializer = t.getInitializer();
    if (initializer) {
        write("=");
        initializer->visit(*this);
    }
}

void AstPrinter::handle(const slang::ast::ScalarType& t) {
    write(t.name);
}

/// variable_port_type ::= var_data_type
/// var_data_type      ::= data_type | var data_type_or_implicit
// data_declaration10 ::=  [ var ] [ lifetime ] data_type_or_implicit
void AstPrinter::handle(const slang::ast::VariableSymbol& t) {
    // without this the module ast doesn't contain the name of the variable for no apparent reason
    if ((t.flags & VariableFlags::RefStatic) != VariableFlags::RefStatic)
        write(t.lifetime == VariableLifetime::Static ? "static" : "automatic");

    const Type& data_type = t.getDeclaredType().get()->getType();
    bitmask<DeclaredTypeFlags> flags = t.getDeclaredType().get()->getFlags();

    if ((flags & DeclaredTypeFlags::InferImplicit) != DeclaredTypeFlags::InferImplicit) {
        write(convertType(data_type.toString()), true, true);
    }

    write(t.name);

    auto initializer = t.getInitializer();
    if (initializer) {
        write("=");
        initializer->visit(*this);
    }
}

void AstPrinter::handle(const slang::ast::MultiPortSymbol& t) {
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
void AstPrinter::handle(const slang::ast::ParameterSymbol& t) {
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
void AstPrinter::handle(const DefinitionSymbol& t) {
    write(t.defaultLifetime == VariableLifetime::Static ? "static" : "automatic");
    write(t.name);
}

/// package_import_item ::= package_identifier :: identifier
void AstPrinter::handle(const ExplicitImportSymbol& t) {
    write(t.packageName);
    write("::", false);
    write(t.importName);
}

// package_import_item ::= package_identifier :: *
void AstPrinter::handle(const WildcardImportSymbol& t) {
    write(t.packageName);
    write("::", false);
    write("*", false);
}

// modport_declaration ::= modport modport_item { , modport_item } ;
// modport declartion with multiple items get automaticly splitted in multiple separete modport
// declartions
void AstPrinter::handle(const ModportSymbol& t) {
    write("modport");
    // modport_item ::= modport_identifier ( modport_ports_declaration { ,
    // modport_ports_declaration } )
    write(t.name);
    write("(");
    auto member = t.getFirstMember();
    while (member) {
        member->visit(*this);
        if (member != t.getLastMember())
            write(",", false);
        member = member->getNextSibling();
    }
    write(")");
}

// net_alias ::= alias net_lvalue = net_lvalue { = net_lvalue } ;
void AstPrinter::handle(const NetAliasSymbol& t) {
    write("alias");
    for (auto expr : t.getNetReferences()) {
        expr->visit(*this);
        if (expr != t.getNetReferences().back())
            write("=");
    }
}
// property_declaration ::=property property_identifier [ ( [ property_port_list ] ) ] ;{
// assertion_variable_declaration }property_spec [ ; ]endproperty
void AstPrinter::handle(const PropertySymbol& t) {
    write("property");
    write(t.name);
    auto member = t.getFirstMember();

    if (!t.ports.empty()) {
        write("(");
        for (auto port : t.ports) {
            port->visit(*this);
            if (port != t.ports.back())
                write(",");
        }
        auto symbol = ((PortSymbol*)t.ports.back())->internalSymbol;
        member = symbol ? symbol->getNextSibling() : t.ports.back();
        write(")");
    }

    write(";\n");
    indentation_level++;

    while (member) {
        member->visit(*this);
        if ("\n" != buffer.substr(buffer.length() - 1, buffer.length() - 1))
            write(";\n", false);
        member = member->getNextSibling();
    }
    indentation_level--;
    write("endproperty\n");
}

// property_port_item ::={ attribute_instance } [ local [ property_lvar_port_direction ] ]
// property_formal_type formal_port_identifier {variable_dimension} [ = property_actual_arg ]
void AstPrinter::handle(const AssertionPortSymbol& t) {
    writeAttributeInstances(t);

    if (t.isLocalVar()) {
        write("local input");
    }

    // write(t.declaredType.getType().toString());

    write(t.name);
}

// modport_ports_declaration ::= { attribute_instance } modport_simple_ports_declaration
// modport_simple_ports_declaration ::= port_direction modport_simple_port { ,modport_simple_port}
void AstPrinter::handle(const ModportPortSymbol& t) {
    writeAttributeInstances(t);
    write(t.direction);
    write(t.name);
}

/// { package_import_declaration } [ parameter_port_list ] [ list_of_port_declarations ];
void AstPrinter::handle(const InstanceBodySymbol& t) {

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
        remainingMember = t.getParameters().back()->symbol.getNextSibling();
        write(")");
    }

    // list_of_port_declarations2 ::=( [ { attribute_instance} ansi_port_declaration { , {
    // attribute_instance} ansi_port_declaration } ] )
    internalSymbols.clear();
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
        
        // the remainingMember shouden't be one of the internal symbols -> skip these
        remainingMember = t.getPortList().back()->getNextSibling();
        while(internalSymbols.count(remainingMember)!=0)
             remainingMember = remainingMember->getNextSibling();
        
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
}

void AstPrinter::handle(const StatementBlockSymbol& t) {
    // extra block  where variables, .. are defined that are used in the corresponding instance,
    // contains mostly redundant except TypeAliasTypes
    t.visit(makeVisitor([&](auto& visitor, const TypeAliasType& TypeAliasType) {
        AstPrinter::handle(TypeAliasType);
        visitor.visitDefault(TypeAliasType);
    }));
}

// loop_generate_construct ::= for ( genvar_initialization ; genvar_expression ; genvar_iteration )
// generate_block
void AstPrinter::handle(const GenerateBlockArraySymbol& t) {
    // als je kijkt naar de ast van een gen block is het ( denk ik) onmgelijk om de originele source
    // te herconstrueren
    // _> deze worden via de originele source code geprint
    write(t.getSyntax()->toString());
}

// TODO: dit beter implementeren
void AstPrinter::handle(const GenerateBlockSymbol& t) {
    write("generate");
    write(t.getSyntax()->toString());
    write("endgenerate\n");

    /*
    auto member = t.getFirstMember();
    while (member) {
        member->visit(*this);

        // TODO betere maniet voor dit vinden
        if ("\n" != buffer.substr(buffer.length() - 1, buffer.length() - 1))
            write(";\n", false);

        member = member->getNextSibling();
    }*/
}

// udp_output_declaration ::= { attribute_instance } output port_identifier
// udp_input_declaration ::= { attribute_instance } input list_of_udp_port_identifiers
void AstPrinter::handle(const PrimitivePortSymbol& t) {
    writeAttributeInstances(t);
    write(t.direction);
    write(t.name);
}

// udp_declaration      ::= udp_ansi_declaration udp_body endprimitive [ : udp_identifier ]
// udp_ansi_declaration ::= {attribute_instance} primitive udp_identifier (
// udp_declaration_port_list ) ;
void AstPrinter::handle(const PrimitiveSymbol& t) {
    writeAttributeInstances(t);
    write("primitive");
    write(t.name);

    // udp_declaration_port_list ::= udp_output_declaration , udp_input_declaration { ,
    // udp_input_declaration }
    write("(");
    for (auto port : t.ports) {
        port->visit(*this);
        if (port != t.ports.back())
            write(",", false);
    }
    write(")\n");
    indentation_level++;

    // udp_body ::= combinational_body | sequential_body
    if (t.isSequential) {
        // sequential_body       ::= [ udp_initial_statement ] table sequential_entry { sequential_entry } endtable
        // udp_initial_statement ::= initial output_port_identifier = init_val ;
        if (t.initVal) {
            write("intial");
            write(t.ports.front()->name);
            write("=");
            write(t.initVal->toString());
        }

        write("table\n");
        // sequential_entry ::= seq_input_list : current_state : next_state ;
        for (auto TableEntry : t.table) {
            std::string entry = std::string(TableEntry.inputs);
            entry.append(1, ':');
            entry.append(1, TableEntry.state);
            entry.append(1, ':');
            entry.append(1, TableEntry.output);
            write(entry + ";\n");
        }
        write("endtable\n");
    }
    else {
        // combinational_body ::= table combinational_entry { combinational_entry } endtable
        write("table\n");
        for (auto TableEntry : t.table) {
            // combinational_entry ::= level_input_list : output_symbol ;
            std::string entry = std::string(TableEntry.inputs);
            entry.append(1, ':');
            entry.append(1, TableEntry.output);
            write(entry + ";\n");
        }
        write("endtable\n");
    }
    indentation_level--;

    write("endprimitive");
}

// config_declaration ::= config config_identifier ; { local_parameter_declaration ;
// }design_statement { config_rule_statement } endconfig [ : config_identifier ]
void AstPrinter::handle(const ConfigBlockSymbol& t) {
    write("config");
    write(t.name);
    write(";\n");
    indentation_level++;

    auto member = t.getFirstMember();
    while (member) {
        member->visit(*this);
        // TODO betere maniet voor dit vinden
        if ("\n" != buffer.substr(buffer.length() - 1, buffer.length() - 1)) {
            write(";\n", false);
        }
        member = member->getNextSibling();
    }

    indentation_level--;
    write("endconfig\n");
}

// specify_block ::= specify { specify_item } endspecify
void AstPrinter::handle(const SpecifyBlockSymbol& t) {
    write("specify");

    indentation_level++;
    auto member = t.getFirstMember();
    while (member) {
        member->visit(*this);
        // TODO betere maniet voor dit vinden
        if ("\n" != buffer.substr(buffer.length() - 1, buffer.length() - 1)) {
            write(";\n", false);
        }
        member = member->getNextSibling();
    }
    indentation_level--;
    
    write("endspecify\n");
}

// specparam_declaration ::= specparam [ packed_dimension ] list_of_specparam_assignments ;
// specparam_assignment  ::= specparam_identifier = constant_mintypmax_expression
void AstPrinter::handle(const SpecparamSymbol& t) {
    write("specparam");
    write(t.name);
    write("=");
    if (t.getInitializer())
        t.getInitializer()->visit(*this);
}

// path_declaration ::=simple_path_declaration ;
//                  | edge_sensitive_path_declaration ;
//                  | state_dependent_path_declaration;
// simple_path_declaration ::=parallel_path_description = path_delay_value
// edge_sensitive_path_declaration ::= parallel_edge_sensitive_path_description = path_delay_value
// state_dependent_path_declaration ::= if ( module_path_expression ) simple_path_declaration
void AstPrinter::handle(const TimingPathSymbol& t) {
    if (t.isStateDependent) {
        write("if (");
        if (t.getConditionExpr())
            t.getConditionExpr()->visit(*this);
        write(")");
    }
    write("(");
    // full_path_description ::=( list_of_path_inputs [ polarity_operator ] *> list_of_path_outputs )
    // specify_input_terminal_descriptor ::=input_identifier [ [ constant_range_expression ] ]
    for (auto input : t.getInputs()) {
        input->visit(*this);
        if (input !=  t.getInputs().back())
            write(",", false);
    }

    if (t.polarity == TimingPathSymbol::Polarity::Positive) {
        write("+", false);
    }
    else if (t.polarity == TimingPathSymbol::Polarity::Negative) {
        write("-", false);
    }

    if (t.connectionKind==TimingPathSymbol::ConnectionKind::Full){
        write("*>");
    } else{
        write("=>");
    }

    for (auto output : t.getOutputs()) {
        output->visit(*this);
        if (output !=  t.getOutputs().back())
            write(",", false);

    }
    write(")=(");

    for (auto delay : t.getDelays()) {
        delay->visit(*this);
        if (delay !=  t.getDelays().back())
            write(",", false);
    }
    write(")");
}

// method_prototype ::= task_prototype | function_prototype
// function_prototype ::= function data_type_or_void function_identifier [ ( [ tf_port_list ] ) ]
// task_prototype ::= task task_identifier [ ( [ tf_port_list ] ) ]
void AstPrinter::handle(const MethodPrototypeSymbol& t) {
    if ((t.flags & MethodFlags::InterfaceExtern) == MethodFlags::InterfaceExtern)
        //extern_tf_declaration ::=extern method_prototype;
        //                         extern forkjoin task_prototype ;
        write("extern");

    if ((t.flags & MethodFlags::ForkJoin) == MethodFlags::ForkJoin)
        write("forkjoin");


    if (((t.flags & MethodFlags::ModportExport) == MethodFlags::ModportExport)){
        write("export");
    }

    if (((t.flags & MethodFlags::ModportImport) == MethodFlags::ModportImport)){
        write("import");
    }

    write(lowerFirstLetter(toString(t.subroutineKind)));
    

    if (t.subroutineKind ==SubroutineKind::Function ){
        write(t.declaredReturnType.getType().toString());
    }

    //function_identifier | task_identifier
    write(t.name);
    
    //tf_port_list
    write("(");
    for (auto arg: t.getArguments()){
        arg->visit(*this);
        if (arg!= t.getArguments().back())
            write(",");
    }
    write(")");
    
}

void AstPrinter::handle(const FormalArgumentSymbol& t) {
    write(t.getType().toString());
    write(t.name);
    if (t.getDefaultValue()){
        write("=");
        t.getDefaultValue()->visit(*this);
    }
}

} // namespace slang::ast