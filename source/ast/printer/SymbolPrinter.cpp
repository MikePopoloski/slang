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
    // if it is already written somewhere else do not write it again
    if (initializedInstances.count(&(t.body)) != 0) {
        return;
    }
    else {
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
        write(")", false);
    }
}

/// ansi_port_declaration ::=[ net_port_header  ] port_identifier { unpacked_dimension } [ =
/// constant_expression ]
///                          | [ variable_port_header ] port_identifier { variable_dimension } [
///                          = constant_expression ]
void AstPrinter::handle(const slang::ast::PortSymbol& t) {
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

void AstPrinter::handle(const slang::ast::ScalarType& t) {
    write(t.name);
}

/// variable_port_type ::= var_data_type
/// var_data_type      ::= data_type | var data_type_or_implicit
// data_declaration10 ::=  [ var ] [ lifetime ] data_type_or_implicit
void AstPrinter::handle(const slang::ast::VariableSymbol& t) {
    write(t.lifetime == VariableLifetime::Static ? "static" : "automatic");

    const Type& data_type = t.getDeclaredType().get()->getType();
    bitmask<DeclaredTypeFlags> flags= t.getDeclaredType().get()->getFlags();
    
    if ((flags & DeclaredTypeFlags::InferImplicit) != DeclaredTypeFlags::InferImplicit){
        write(convertType(data_type.toString()),true,true);
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
    visitDefault(t);
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

// modport_ports_declaration ::= { attribute_instance } modport_simple_ports_declaration
// modport_simple_ports_declaration ::= port_direction modport_simple_port { ,
// modport_simple_port}
//
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

        if (t.getPortList().back()->kind == SymbolKind::Port) {
            auto symbol = ((PortSymbol*)t.getPortList().back())->internalSymbol;
            remainingMember = symbol ? symbol->getNextSibling() : t.getPortList().back();
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
void AstPrinter::handle(const PrimitivePortSymbol& t){
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
            entry.append(1,':');
            entry.append(1,TableEntry.state);
            entry.append(1,':');
            entry.append(1,TableEntry.output);
            write(entry+";\n");
        }
        write("endtable\n");
    }
    else {
        // combinational_body ::= table combinational_entry { combinational_entry } endtable
        write("table\n");
        for (auto TableEntry : t.table) {
            //combinational_entry ::= level_input_list : output_symbol ;
            std::string entry = std::string(TableEntry.inputs);
            entry.append(1,':');
            entry.append(1,TableEntry.output);
            write(entry+";\n");
        }
        write("endtable\n");
    }
    indentation_level--;

    write("endprimitive");
}
} // namespace slang::ast