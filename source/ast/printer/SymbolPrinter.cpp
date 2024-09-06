//------------------------------------------------------------------------------
//! @file ExpressionPrinter.cpp
//! @brief adds Support for printing expressions from the ast
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "slang/ast/Symbol.h"
#include "slang/ast/printer/defaultAstPrinter.h"
#include "slang/ast/symbols/CoverSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/util/Util.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

// genvar_initialization ::= [ genvar ] genvar_identifier = constant_expression
void AstPrinter::handle(const GenvarSymbol& t) {
    currSymbol = &t;
    write("genvar");
    write(t.name);
}

// attr_spec ::= attr_name [ = constant_expression ]
// attr_name ::= identifier
void AstPrinter::handle(const AttributeSymbol& t) {
    currSymbol = &t;
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
    currSymbol = &t;
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
    currSymbol = &t;
    write("program;\n");
    visitDefault(t);
    write("endprogram");
}

// ding zoals initial
void AstPrinter::handle(const ProceduralBlockSymbol& t) {
    currSymbol = &t;
    write(t.procedureKind);

    t.getBody().visit(*this);
}

// continuous_assign ::= assign [ drive_strength ] [ delay3 ] list_of_net_assignments ;
//                     | assign [ delay_control ] list_of_variable_assignments ;
void AstPrinter::handle(const ContinuousAssignSymbol& t) {
    currSymbol = &t;
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
    currSymbol = &t;
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
        // module_instantiation ::= module_identifier [ parameter_value_assignment ] hierarchical_instance { , hierarchical_instance } ;
        writeName(t.body);
        // TODO parameter_value_assignment

        // hierarchical_instance ::= name_of_instance ( [ list_of_port_connections ] ) | named_port_connection { , named_port_connection }
        write(t.name);
        write("(", false);
        // list_of_port_connections ::= named_port_connection { , named_port_connection } or named equivalent
        for (auto named_port : t.getPortConnections()) {
            // named_port_connection ::= { attribute_instance } . port_identifier [ ( [expression ] ) ]
            writeAttributeInstances(named_port->port);
            write(".");
            writeName(named_port->port, false);
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

// ansi_port_declaration ::=  [ net_port_header  ] port_identifier { unpacked_dimension } [=constant_expression ]
//                          | [ variable_port_header ] port_identifier { variable_dimension } [= constant_expression ]
void AstPrinter::handle(const slang::ast::PortSymbol& t) {
    currSymbol = &t;
    // net_port_header      ::= [ port_direction ] net_port_type
    // variable_port_header ::= [ port_direction ] variable_port_type

    internalSymbols.insert({t.internalSymbol, t.direction});

    if (!t.isAnsiPort) {
        return handleNonAnsiPort(t);
    }

    if (t.internalSymbol) {
        // direction is handeld via the internalSymbols map
        t.internalSymbol->visit(*this);
    }
    else {
        write(t.direction);
        if (t.getType().toString() == "void") {
            write(".$()", true, true);
            write(t.name, false);
        }
        else {
            write(convertType(t.getType().toString()), true, true);
        }
    }

    if (t.getInternalExpr())
        t.getInternalExpr()->visit(*this);

    if (t.getInitializer()) {
        write("=", false);
        t.getInitializer()->visit(*this);
    }
}

///(non ansi) port ::=[ port_expression ] | . port_identifier ( [ port_expression ] )
/// port_reference ::= port_identifier constant_select
void AstPrinter::handleNonAnsiPort(const slang::ast::PortSymbol& t) {
    currSymbol = &t;
    write(t.name);
    if (t.getInternalExpr())
        t.getInternalExpr()->visit(*this);
}

/// ansi_port_declaration ::=[ interface_port_header ] port_identifier { unpacked_dimension } [
/// = constant_expression ]
void AstPrinter::handle(const slang::ast::InterfacePortSymbol& t) {
    currSymbol = &t;
    // interface_port_header ::= interface_identifier [ . modport_identifier]
    if (t.interfaceDef) {
        writeName(*t.interfaceDef);
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
}

/// net_port_type ::= [ net_type ] data_type_or_implicit
void AstPrinter::handle(const slang::ast::NetSymbol& t) {
    if (t.isImplicit){
        return;
    }
    currSymbol = &t;
    // add the direction if this symbol is part of the port declaration
    if (internalSymbols.count(&t) != 0)
        write(internalSymbols[&t]);

    write(t.netType.netKind);
    write(convertType(t.getType().toString()), true, true);
    write(t.name);

    auto initializer = t.getInitializer();
    if (initializer) {
        write("=");
        initializer->visit(*this);
    }
}

void AstPrinter::handle(const slang::ast::ScalarType& t) {
    currSymbol = &t;
    write(t.name);
}

/// variable_port_type ::= var_data_type
/// var_data_type      ::= data_type | var data_type_or_implicit
// data_declaration10 ::=  [ var ] [ lifetime ] data_type_or_implicit
void AstPrinter::handle(const slang::ast::VariableSymbol& t) {
    currSymbol = &t;
    // add the direction if this symbol is part of the port declaration
    if (t.flags.has(VariableFlags::CompilerGenerated) | t.flags.has(VariableFlags::isDuplicate))
        return;

    bool isPort = internalSymbols.count(&t) != 0;
    if (isPort)
        write(internalSymbols[&t]);

    write("var");
    // without this the module ast doesn't contain the name of the variable for no apparent reason
    //( after processing the new source code)
    if (!t.flags.has(VariableFlags::RefStatic) && !isPort)
        write(t.lifetime == VariableLifetime::Static ? "static" : "automatic");

    if (t.flags.has(VariableFlags::CheckerFreeVariable))
        write("rand");

    const Type& data_type = t.getDeclaredType().get()->getType();
    bitmask<DeclaredTypeFlags> flags = t.getDeclaredType().get()->getFlags();

    if ((flags & DeclaredTypeFlags::InferImplicit) != DeclaredTypeFlags::InferImplicit) {
        write(convertType(data_type.toString()), true, true);
    }

    writeAttributeInstances(t);

    write(t.name);

    auto initializer = t.getInitializer();
    if (initializer) {
        write("=");
        initializer->visit(*this);
    }
}
void AstPrinter::handle(const slang::ast::ClassPropertySymbol& t) {
    currSymbol = &t;
    if (t.randMode != RandMode::None) {
        write(lower(toString(t.randMode)));
    }
    const VariableSymbol& u = t;
    this->handle(u);
}

void AstPrinter::handle(const slang::ast::MultiPortSymbol& t) {
    currSymbol = &t;
    if (t.isNullPort) {
        return visitDefault(t);
    }

    // write(t.direction);

    // write(convertType(t.getType().toString()), true, true);
    write(".");
    write(t.name, false);
    write("({", false);

    visitMembers<>(t.ports);

    write("})");
}

/// parameter_declaration       ::= parameter data_type_or_implicit list_of_param_assignments
/// local_parameter_declaration ::= localparam data_type_or_implicit list_of_param_assignments
/// list_of_param_assignments   ::= param_assignment { , param_assignment }  always has a lenght 1
/// ?? param_assignment         ::= parameter_identifier { unpacked_dimension } [ =
/// constant_param_expression ]
void AstPrinter::handle(const slang::ast::ParameterSymbol& t) {
    currSymbol = &t;
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
    currSymbol = &t;
    write(t.defaultLifetime == VariableLifetime::Static ? "static" : "automatic");
    write(t.name);
}

/// package_import_item ::= package_identifier :: identifier
void AstPrinter::handle(const ExplicitImportSymbol& t) {
    currSymbol = &t;
    write(t.packageName);
    write("::", false);
    write(t.importName);
}

// package_import_item ::= package_identifier :: *
void AstPrinter::handle(const WildcardImportSymbol& t) {
    currSymbol = &t;
    write(t.packageName);
    write("::", false);
    write("*", false);
}

// modport_declaration ::= modport modport_item { , modport_item } ;
// modport declartion with multiple items get automaticly splitted in multiple separete modport
// declartions
void AstPrinter::handle(const ModportSymbol& t) {
    currSymbol = &t;
    write("modport");
    // modport_item ::= modport_identifier ( modport_ports_declaration { ,
    // modport_ports_declaration } )
    write(t.name);
    write("(");
    auto member = t.getFirstMember();
    visitMembers(member, ",",false);
    write(")");
}

// net_alias ::= alias net_lvalue = net_lvalue { = net_lvalue } ;
void AstPrinter::handle(const NetAliasSymbol& t) {
    write("alias");
    visitMembers<>(t.getNetReferences(), "=");
}
// property_declaration ::=property property_identifier [ ( [ property_port_list ] ) ] ;{
// assertion_variable_declaration }property_spec [ ; ]endproperty
void AstPrinter::handle(const PropertySymbol& t) {
    currSymbol = &t;
    write("property");
    write(t.name);
    auto member = t.getFirstMember();

    if (!t.ports.empty()) {
        write("(");
        visitMembers<>(t.ports);
        auto symbol = ((PortSymbol*)t.ports.back())->internalSymbol;
        member = symbol ? symbol->getNextSibling() : t.ports.back();
        write(")");
    }

    write(";\n");
    indentation_level++;

    visitMembers(member, ";");

    indentation_level--;
    write("endproperty\n");
}

// property_port_item ::={ attribute_instance } [ local [ property_lvar_port_direction ] ]
// property_formal_type formal_port_identifier {variable_dimension} [ = property_actual_arg ]
void AstPrinter::handle(const AssertionPortSymbol& t) {
    currSymbol = &t;
    writeAttributeInstances(t);

    if (t.isLocalVar()) {
        write("local input");
    }

    write(t.declaredType.getType().toString());

    write(t.name);
}

// modport_ports_declaration ::= { attribute_instance } modport_simple_ports_declaration
// modport_simple_ports_declaration ::= port_direction modport_simple_port { ,modport_simple_port}
void AstPrinter::handle(const ModportPortSymbol& t) {
    currSymbol = &t;
    writeAttributeInstances(t);
    write(t.direction);
    write(t.name);
}

/// { package_import_declaration } [ parameter_port_list ] [ list_of_port_declarations ];
void AstPrinter::handle(const InstanceBodySymbol& t) {
    currSymbol = &t;
    
    auto remainingMember = t.getFirstMember();

    // package_import_declaration ::= import package_import_item { , package_import_item } ;
    auto wildCard = t.getWildcardImportData();
    if (wildCard) {
        write("import");
        for (auto imports : wildCard->wildcardImports) {

            int currentBuffer = changedBuffer;

            imports->visit(*this);
            if (changedBuffer != currentBuffer && imports != wildCard->wildcardImports.back())
                write(",", false);
        }
        write(";", false);
    }

    // parameter_port_list ::= # ( list_of_param_assignments { , parameter_port_declaration } )
    if (!t.getParameters().empty()) {
        write("#(", false);
        for (auto param : t.getParameters()) {
            if (param->isBodyParam())
                continue;
            int currentBuffer = changedBuffer;

            param->symbol.visit(*this);

            if (changedBuffer != currentBuffer && param != t.getParameters().back())
                write(",", false);

            // implemented like this to prevent body parameters shifting the last parameters
            remainingMember = param->symbol.getNextSibling();
        }

        write(")");
    }

    // list_of_port_declarations2 ::=( [ { attribute_instance} ansi_port_declaration { , {
    // attribute_instance} ansi_port_declaration } ] )
    if (!t.getPortList().empty()) {

        write(std::string_view("("), false);
        bool isAnsi = false;

        for (auto port : t.getPortList()) {

            if (!port)
                continue;
            writeAttributeInstances(*port);

            port->visit(*this);

            if (!isAnsi && port->kind == SymbolKind::Port) {
                isAnsi = ((slang::ast::PortSymbol*)port)->isAnsiPort;
            }

            if (port != t.getPortList().back())
                write(",", false);
        }

        // the remainingMember shouden't be one of the internal symbols -> skip these
        remainingMember = t.getPortList().back()->getNextSibling();
        while (isAnsi && internalSymbols.count(remainingMember) != 0 && remainingMember)
            remainingMember = remainingMember->getNextSibling();

        write(")");
    }

    write(";\n", false);

    // return if there are no remaining members
    visitMembers(remainingMember, ";");
}

void AstPrinter::handle(const StatementBlockSymbol& t) {
    currSymbol = &t;
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
    currSymbol = &t;
    // als je kijkt naar de ast van een gen block is het ( denk ik) onmgelijk om de originele source
    // te herconstrueren
    // _> deze worden via de originele source code geprint
    write(t.getSyntax()->toString());
}

// TODO: implementent this without using the getSyntax function
void AstPrinter::handle(const GenerateBlockSymbol& t) {
    currSymbol = &t;
    write("generate");
    write(t.getSyntax()->toString());
    write("endgenerate\n");
}

// udp_output_declaration ::= { attribute_instance } output port_identifier
// udp_input_declaration ::= { attribute_instance } input list_of_udp_port_identifiers
void AstPrinter::handle(const PrimitivePortSymbol& t) {
    currSymbol = &t;
    writeAttributeInstances(t);
    write(t.direction);
    write(t.name);
}

// udp_declaration      ::= udp_ansi_declaration udp_body endprimitive [ : udp_identifier ]
// udp_ansi_declaration ::= {attribute_instance} primitive udp_identifier (
// udp_declaration_port_list ) ;
void AstPrinter::handle(const PrimitiveSymbol& t) {
    currSymbol = &t;
    writeAttributeInstances(t);
    write("primitive");
    write(t.name);

    // udp_declaration_port_list ::= udp_output_declaration , udp_input_declaration { ,
    // udp_input_declaration }
    write("(");
    visitMembers<>(t.ports);
    write(")\n");
    indentation_level++;

    // udp_body ::= combinational_body | sequential_body
    if (t.isSequential) {
        // sequential_body       ::= [ udp_initial_statement ] table sequential_entry {
        // sequential_entry } endtable udp_initial_statement ::= initial output_port_identifier =
        // init_val ;
        if (t.initVal) {
            write("intial");
            writeName(*t.ports.front());
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
    currSymbol = &t;
    write("config");
    write(t.name);
    write(";\n");
    indentation_level++;

    auto member = t.getFirstMember();
    visitMembers(member, ";");

    indentation_level--;
    write("endconfig\n");
}

// specify_block ::= specify { specify_item } endspecify
void AstPrinter::handle(const SpecifyBlockSymbol& t) {
    currSymbol = &t;
    write("specify");

    indentation_level++;
    auto member = t.getFirstMember();
    visitMembers(member);

    indentation_level--;

    write("endspecify\n");
}

// specparam_declaration ::= specparam [ packed_dimension ] list_of_specparam_assignments ;
// specparam_assignment  ::= specparam_identifier = constant_mintypmax_expression
void AstPrinter::handle(const SpecparamSymbol& t) {
    currSymbol = &t;
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
    currSymbol = &t;
    if (t.isStateDependent) {
        write("if (");
        if (t.getConditionExpr())
            t.getConditionExpr()->visit(*this);
        write(")");
    }
    write("(");
    // full_path_description ::=( list_of_path_inputs [ polarity_operator ] *> list_of_path_outputs
    // ) specify_input_terminal_descriptor ::=input_identifier [ [ constant_range_expression ] ]
    visitMembers<>(t.getInputs());

    if (t.polarity == TimingPathSymbol::Polarity::Positive) {
        write("+", false);
    }
    else if (t.polarity == TimingPathSymbol::Polarity::Negative) {
        write("-", false);
    }

    if (t.connectionKind == TimingPathSymbol::ConnectionKind::Full) {
        write("*>");
    }
    else {
        write("=>");
    }
    visitMembers<>(t.getOutputs());

    write(")=(");
    visitMembers<>(t.getDelays());
    write(")");
}

// method_prototype ::= task_prototype | function_prototype
// function_prototype ::= function data_type_or_void function_identifier [ ( [ tf_port_list ] ) ]
// task_prototype ::= task task_identifier [ ( [ tf_port_list ] ) ]
template<IsFunc T>
void AstPrinter::handle(const T& t) {
    currSymbol = &t;
    // Ignore built-in methods on class types.
    if (t.flags.has(MethodFlags::BuiltIn | MethodFlags::Randomize))
        return;

    if (t.flags.has(MethodFlags::Virtual))
        write("virtual");

    if (t.flags.has(MethodFlags::Pure))
        write("pure virtual");

    if (((t.flags & MethodFlags::Static) == MethodFlags::Static)) {
        write("static");
    }

    if (t.flags.has(MethodFlags::InterfaceExtern))
        // extern_tf_declaration ::=extern method_prototype;
        //                          extern forkjoin task_prototype ;
        write("extern");

    if (t.flags.has(MethodFlags::Constructor))
        write("new");

    if (t.flags.has(MethodFlags::DPIImport))
        write(R"(import "DPI")");

    if (t.flags.has(MethodFlags::DPIContext))
        write(R"(import "DPI" context)");

    if (t.flags.has(MethodFlags::Initial))
        write(R"(initial)");

    if (t.flags.has(MethodFlags::Extends))
        write("extends");

    if (t.flags.has(MethodFlags::Final))
        write("final");

    if ((t.flags & MethodFlags::ForkJoin) == MethodFlags::ForkJoin)
        write("forkjoin");

    if (((t.flags & MethodFlags::ModportExport) == MethodFlags::ModportExport)) {
        write("export");
    }

    if (((t.flags & MethodFlags::ModportImport) == MethodFlags::ModportImport)) {
        write("import");
    }

    write(lowerFirstLetter(toString(t.subroutineKind)));

    if (t.subroutineKind == SubroutineKind::Function) {
        write(t.declaredReturnType.getType().toString());
    }

    // function_identifier | task_identifier
    write(t.name);

    // tf_port_list
    write("(", false);
    for (auto arg : t.getArguments()) {
        arg->visit(*this);
        if (arg != t.getArguments().back())
            write(",", false);
    }
    write(")", false);

    if (t.isKind(SymbolKind::Subroutine)) {
        write(";\n", false);
        ((const SubroutineSymbol&)t).getBody().visit(*this);
        write("end");
        write(lowerFirstLetter(toString(t.subroutineKind)), false);
        write("\n", false);
    }
}

void AstPrinter::handle(const FormalArgumentSymbol& t) {
    currSymbol = &t;
    write(t.getType().toString());
    write(t.name);
    if (t.getDefaultValue()) {
        write("=");
        t.getDefaultValue()->visit(*this);
    }
}

void AstPrinter::handle(const UninstantiatedDefSymbol& t) {
    currSymbol = &t;
    // module_instantiation ::= module_identifier [ parameter_value_assignment ]
    // hierarchical_instance { , hierarchical_instance } ;
    write(t.definitionName);
    write(t.name);

    write("(", false);

    for (auto port : t.getPortConnections()) {
        port->visit(*this);

        if (port != t.getPortConnections().back())
            write(",", false);
    }
    write(");\n", false);
}

void AstPrinter::handle(const CompilationUnitSymbol& t) {
    currSymbol = &t;
    visitDefault(t);
    // TypeAliases can also be attached to a compilationUnit
    write(blockBuffer);
    blockBuffer = "";
}
// checker_declaration ::= checker checker_identifier [ ( [ checker_port_list ] ) ] ; { {
// attribute_instance } checker_or_generate_item } endchecker [ : checker_identifier ]
void AstPrinter::handle(const CheckerSymbol& t) {
    currSymbol = &t;
    write("checker");
    write(t.name);
    write("(");

    auto remainingMember = t.getFirstMember();

    for (auto port : t.ports) {
        indentation_level++;
        port->visit(*this);

        // default value is only availible as a syntax node -> print its string representation
        if (port->defaultValueSyntax){
            write("=");
            write(port->defaultValueSyntax->toString());
        }

        if (port != t.ports.back())
            write(",\n", false);
        else
            remainingMember = port->getNextSibling();
        indentation_level--;
    }

    write(");\n");
    //  { { attribute_instance } checker_or_generate_item }

    // if a CheckerInstanceBodySymbol is in the ast it will find this comment and replace it with
    // the content of the body
    std::string identifier = "//" + std::to_string((unsigned long long)(void*)&t);
    write(identifier);

    write("endchecker\n");
}

void AstPrinter::handle(const CheckerInstanceSymbol& t) {
    currSymbol = &t;
    t.body.visit(*this);
    // checker_instantiation ::= ps_checker_identifier name_of_instance (
    // [list_of_checker_port_connections] ) ;
    if (!t.getPortConnections().empty()) {
        write(t.body.name);
        write(t.name);
        write("(");
        // list_of_checker_port_connections
        for (auto conn : t.getPortConnections()) {
            // named_checker_port_connection ::= { attribute_instance } . formal_port_identifier [ (
            // [ property_actual_arg ] ) ]
            std::visit(
                [&](auto&& arg) {
                    if (arg)
                        arg->visit(*this);
                },
                conn.actual);

            if (&conn.formal != &t.getPortConnections().back().formal)
                write(",", false);
        }
        write(")");
    }
}

// the body needs to be added to the checker symbol, there is no pointer from there to here so
// when the symbol is visited it wil leave a comment with its memory adress this function will make
// a string containing the body and inserting it in the correct location
void AstPrinter::handle(const CheckerInstanceBodySymbol& t) {
    currSymbol = &t;
    auto remainingMember = t.getFirstMember();

    // remove the ports
    while (remainingMember && remainingMember->kind == SymbolKind::AssertionPort)
        remainingMember = remainingMember->getNextSibling();

    std::string programBuffer;
    this->tempBuffer = &programBuffer;

    this->useTempBuffer = true;
    visitMembers(remainingMember, ";");
    this->useTempBuffer = false;

    // while elaborating the name of the port is replaced with the name of the argument
    std::string checker_identifier = R"(\/\/)" +
                                     std::to_string((unsigned long long)(void*)&t.checker);
    std::regex reg(checker_identifier);

    this->buffer = std::regex_replace(this->buffer, reg, programBuffer);
}

/*
clocking_declaration ::= [ default ] clocking [ clocking_identifier ] clocking_event ;{
clocking_item }endclocking [ : clocking_identifier ] | global clocking [ clocking_identifier ]
clocking_event ; endclocking [ : clocking_identifier]
*/
void AstPrinter::handle(const ClockingBlockSymbol& t) {
    currSymbol = &t;
    write("default clocking");
    write(t.name);
    t.getEvent().visit(*this);
    write(";\n");

    visitMembers(t.getFirstMember(), ";");

    write("endclocking\n");
}

// TODO: Adding the right information to the ast to make this possible
void AstPrinter::handle(const GenericClassDefSymbol& t) {
    currSymbol = &t;
    write(t.getSyntax()->toString());
    write("endclass \n");
}

// constraint_declaration ::= [ static ] constraint constraint_identifier constraint_block
void AstPrinter::handle(const ConstraintBlockSymbol& t) {
    currSymbol = &t;
    if (t.flags.has(ConstraintBlockFlags::Static))
        write("static");
    write("constraint");
    write(t.name);
    // constraint_block ::= { { constraint_block_item } }
    write("{\n");
    indentation_level++;

    t.getConstraints().visit(*this);
    indentation_level--;

    write("}");
}

//severity_system_task ::=  $fatal [ ( finish_number [, list_of_arguments ] ) ] ;
//                        | $error [ ( [ list_of_arguments ] ) ] ;
//                        | $warning [ ( [ list_of_arguments ] ) ] ;
//                        | $info [ ( [ list_of_arguments ] ) ] ;
void AstPrinter::handle(const ElabSystemTaskSymbol& t) {
    if(t.taskKind !=ElabSystemTaskKind::StaticAssert){
        write("$");
        write(lowerFirstLetter(toString(t.taskKind)),false);
        if(t.getMessage().has_value()){
            write("(\"",false);
            write(t.getMessage().value());
            write("\")");
        }
    }
    
}

// production ::= [ data_type_or_void ] production_identifier [ ( tf_port_list ) ] : rs_rule { |
// rs_rule } ;
void AstPrinter::handle(const RandSeqProductionSymbol& t) {
    currSymbol = &t;
    write(t.name, false);
    if (!t.arguments.empty()) {
        write("(");
        visitMembers(t.arguments);
        write(")");
    }
    // tf_port_list apears to be unimplemented
    write(":");
    handle(t.getRules());
    write(";\n");
    if (t.getNextSibling() != nullptr &&
        t.getNextSibling()->kind == SymbolKind::RandSeqProduction) {
        t.getNextSibling()->visit(*this);
    }
}

// rs_case_item ::=case_item_expression { , case_item_expression } : production_item ;
void AstPrinter::handle(const RandSeqProductionSymbol::CaseItem& t) {
    visitMembers(t.expressions, ",");
    write(":", false);
    handle(t.item);
}

void AstPrinter::handle(const RandSeqProductionSymbol::ProdBase& t) {
    switch (t.kind) {
        // production_item ::= production_identifier [ ( list_of_arguments ) ]
        case (RandSeqProductionSymbol::ProdKind::Item): {
            auto prodItem = ((const RandSeqProductionSymbol::ProdItem&)t);
            write(prodItem.target->name);
            if (!prodItem.args.empty()) {
                write("(", false);
                visitMembers(prodItem.args);
                write(")", false);
            }
            break;
        }
        // rs_code_block ::= { { data_declaration } { statement_or_null } }
        case (RandSeqProductionSymbol::ProdKind::CodeBlock): {
            write("{");
            auto codeBlock = (const RandSeqProductionSymbol::CodeBlockProd&)t;
            codeBlock.block->visit(*this);
            write("}");
            break;
        }
        // rs_if_else ::= if ( expression ) production_item [ else production_item ]
        case (RandSeqProductionSymbol::ProdKind::IfElse): {
            write("if(");
            auto ifElseItem = (const RandSeqProductionSymbol::IfElseProd&)t;
            ifElseItem.expr->visit(*this);
            write(")");
            ifElseItem.ifItem.visit(*this);
            if (ifElseItem.elseItem.has_value()) {
                write("else");
                handle(ifElseItem.elseItem.value());
            }
            break;
        }
        // rs_repeat ::= repeat ( expression ) production_item
        case (RandSeqProductionSymbol::ProdKind::Repeat): {
            write("repeat(");
            auto repeatItem = (const RandSeqProductionSymbol::RepeatProd&)t;
            repeatItem.expr->visit(*this);
            write(")");
            handle(repeatItem.item);
            break;
        }

        // rs_case ::= case ( case_expression ) rs_case_item { rs_case_item } endcase
        case (RandSeqProductionSymbol::ProdKind::Case): {
            write("case(");
            auto caseItem = (const RandSeqProductionSymbol::CaseProd&)t;
            caseItem.expr->visit(*this);
            write(")\n");
            indentation_level ++;
            visitMembers(caseItem.items, ";",true);
            // rs_case_item:= default [ : ] production_item ;
            if (caseItem.defaultItem.has_value()) {
                write("default :");
                handle(caseItem.defaultItem.value());
                write(";\n");
            }          
              indentation_level--;
            write("endcase");

            break;
        }
    }
}

// rs_rule ::= rs_production_list [ := weight_specification [ rs_code_block ] ]
void AstPrinter::handle(std::span<const RandSeqProductionSymbol::Rule> t) {

    // rs_rule ::= rs_production_list [ := weight_specification [ rs_code_block ] ]
    for (int i = 0; i < t.size(); i++) {
        auto rule = t[i];
        // rs_production_list ::= rs_prod { rs_prod }
        //                     | rand join [ ( expression ) ] production_item production_item {
        //                     production_item }
        if (rule.isRandJoin) {
            write("rand join");

            if (rule.randJoinExpr){
                write("(", false);
                rule.randJoinExpr->visit(*this);
                write(")", false);
            }
        }
        visitMembers(rule.prods," ");
        if (rule.weightExpr != nullptr) {
            write(":=(");
            rule.weightExpr->visit(*this);
            write(")");
            if (rule.codeBlock.has_value())
                handle(rule.codeBlock.value());
        }

        if (i != t.size() - 1) {
            write("|");
        }
    }
}

// cover_point ::=[ [ data_type_or_implicit ] cover_point_identifier : ] coverpoint expression [ iff
// ( expression ) ] bins_or_empty
void AstPrinter::handle(const CoverpointSymbol& t) {
    currSymbol = &t;
    if (t.name != "") {
        write(t.declaredType.getType().toString());
        write(t.name);
        write(":");
    }

    write("coverpoint");

    t.getCoverageExpr().visit(*this);
    if (t.getIffExpr()) {
        write("iff");
        write("(");
        t.getIffExpr()->visit(*this);
        write(")");
    }

    write("{");
    indentation_level++;

    if (!t.options.empty()) {
        write("\n", false);
        visitMembers(t.options, ";", true);
    }

    for (auto& member : t.members()) {
        // BinsSelectExpr.
        if (member.kind == SymbolKind::CoverageBin) {
            int currentBuffer = changedBuffer;
            member.visit(*this);
            if (currentBuffer != changedBuffer)
                write(";\n");
        }
    }

    indentation_level--;
    write("}");
}

// cover_cross ::=[ cross_identifier : ] cross list_of_cross_items [ iff ( expression ) ] cross_body
void AstPrinter::handle(const CoverCrossSymbol& t) {
    currSymbol = &t;
    if (t.name != "") {
        write(t.name);
        write(":");
    }

    write("cross");

    for (auto& target : t.targets) {
        write(target->name);
        if (target != t.targets.back()) {
            write(",");
        }
    }

    if (t.getIffExpr()) {
        write("iff");
        write("(");
        t.getIffExpr();
        write(")");
    }

    write("{");
    indentation_level++;

    if (!t.options.empty()) {
        write("\n", false);
        visitMembers(t.options, ";", true);
    }

    for (auto& member : t.members()) {
        // BinsSelectExpr.
        if (member.kind == SymbolKind::CoverCrossBody) {
            member.visit(*this);
        }
    }

    indentation_level--;
    write("}");
}

// cross_body ::= { { cross_body_item ; } }
void AstPrinter::handle(const CoverCrossBodySymbol& t) {
    currSymbol = &t;
    for (auto& member : t.members()) {
        // BinsSelectExpr.
        // cross_body_item ::=function_declaraton| bins_selection_or_option
        if (member.kind != SymbolKind::TypeAlias) {
            int currentBuffer = changedBuffer;
            member.visit(*this);
            if (currentBuffer != changedBuffer)
                write(";\n");
        }
    }
}

// bins_or_options ::=[ wildcard ] bins_keyword bin_identifier [ [ [ covergroup_expression ] ] ] = {
// covergroup_range_list } [ with ( with_covergroup_expression ) ] [ iff ( expression ) ]
// bins_or_options ::= bins_keyword bin_identifier [ [ [ covergroup_expression ] ] ] = default [ iff
// ( expression ) ]
void AstPrinter::handle(const CoverageBinSymbol& t) {
    currSymbol = &t;
    if (t.isWildcard) {
        write("wildcard");
    }
    write(t.binsKind);

    write(t.name);
    if (!t.isDefaultSequence) {
        if (t.isArray) {
            write("[", false);
            if (t.getSetCoverageExpr())
                t.getSetCoverageExpr()->visit(*this);
            write("]=", false);
        }

        if (!t.getValues().empty() && !t.isDefault) {
            write("{");
            visitMembers(t.getValues());
            write("};");
        }
        else if (!t.getTransList().empty() && !t.isDefault) {
            // getTransList returns a list of transSets which is made up tramsRangeLitst=
            visitTransSet(t.getTransList());
            write("default");
        }
        else if (t.getCrossSelectExpr() != nullptr && !t.isDefault)
            t.getCrossSelectExpr()->visit(*this);
        else if (t.isDefault)
            write("default");
        else
            SLANG_UNREACHABLE;
    }
    else {
        write("= default sequence");
    }
}

void AstPrinter::visitTransList(std::span<const CoverageBinSymbol::TransRangeList> set) {
    for (auto& list : set) {
        // trans_set ::= trans_range_list { => trans_range_list }
        // trans_range_list ::=trans_item| trans_item [* repeat_range ]| trans_item [–> repeat_range
        // ]| trans_item [= repeat_range ]
        visitMembers(list.items);
        if (list.repeatKind != CoverageBinSymbol::TransRangeList::RepeatKind::None) {
            write("[");
            write(list.repeatKind);
            if (list.repeatFrom) {
                list.repeatFrom->visit(*this);
                if (list.repeatTo) {
                    write(":");
                    list.repeatTo->visit(*this);
                }
            }
            write("]");
        }
        if (&set.back() != &list) {
            write("=>");
        }
    }
}

// trans_list ::= ( trans_set ) { , ( trans_set ) }
void AstPrinter::visitTransSet(std::span<const CoverageBinSymbol::TransSet> list) {

    for (auto& set : list) {
        write("(");
        // trans_set ::= trans_range_list { => trans_range_list }
        // trans_range_list ::=trans_item| trans_item [* repeat_range ]| trans_item [–> repeat_range
        // ]| trans_item [= repeat_range ]
        visitTransList(set);

        write(")");
        if (&list.back() != &set)
            write(",");
    }
}

void AstPrinter::handle(const CovergroupBodySymbol& t) {
    currSymbol = &t;
    // visit everything except for the class propertys
    for (auto& member : t.members()) {
        if (member.kind == SymbolKind::ClassProperty)
            continue;
        else {
            int currentBuffer = changedBuffer;
            member.visit(*this);
            if (changedBuffer != currentBuffer)
                write(";\n");
        }
    }
    visitMembers(t.options);
}

} // namespace slang::ast