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
#include <regex>
#include <string>
#include <list>
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
class AstPrinter : public ASTVisitor<AstPrinter, true, true> {
public:
    AstPrinter(slang::ast::Compilation& compilation): compilation(compilation){ };

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

    //@fuure jeff->line 255 ben ik gestqrt
    //#test schrijven
    void handle(const InvalidStatement& t) {
        // wrap the invalid part of the code in a comment
        // print instance
        if (t.child) {
            write("/* invalid code:");
            t.child->visit(*this);
            write("*/");
        }
        else {
            SLANG_UNREACHABLE;
        }
        // todo deze functie en die van invalidAssertionExpr joinen
    }
    
    //#test schrijven
    void handle(const InvalidAssertionExpr& t) {
        // wrap the invalid part of the code in a comment
        // print instance
        if (t.child) {
            write("/* invalid code:");
            t.child->visit(*this);
            write("*/");
        }
        else {
            SLANG_UNREACHABLE;
        }
    }

    //#test schrijven
    void handle(const EmptyStatement& t) {
        // Represents an empty statement, used as a placeholder or an anchor for attributes.
        visitDefault(t);
    }

    //#test schrijven
    void handle(const StatementList& t) {
        // Represents a list of statements.
        visitDefault(t);
    }

    //#test schrijven
    void handle(const BlockStatement& t) {
        // Represents a sequential or parallel block statement.
        if (t.blockKind == StatementBlockKind::Sequential) {
            write("begin");
        }
        else {
            write("fork");
        }

        if (t.blockSymbol) {
            write(":", false);
            writeStatementBlockSymbol(*t.blockSymbol);
            write("\n");
        }
        else {
            write("\n");
        }

        indentation_level += 1;
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

    // attr_spec ::= attr_name [ = constant_expression ]
    // attr_name ::= identifier
    void handle(const AttributeSymbol& t){
        write(t.name);
        if (auto value = t.getValue(); value){
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
    void handle(const PackageSymbol& t){
        // attribute_instance ::= (* attr_spec { , attr_spec } *)
        writeAttributeInstances(t);
    
        write("package");

        write(t.defaultLifetime == VariableLifetime::Static ? "static" : "automatic");
        
        write(t.name);
        write(";\n",false);

        // I chose one type, info about the used declaration is not availble
        // timeunit time_literal [ / time_literal ] ;
        writeTimeUnitsDeclaration(t.timeScale);
    
        visitDefault(t);

        write("endpackage");
    }

    //anonymous_program ::= program ; { anonymous_program_item } endprogram
    void handle(const AnonymousProgramSymbol& t) {
        write("program;\n");
        visitDefault(t);
        write("endprogram");
    }

    // ding zoals initial
    void handle(const ProceduralBlockSymbol& t) {
        write(lowerFirstLetter(toString(t.procedureKind)));
        visitDefault(t);
    }


    /// module_declaration    ::= module_ansi_header [ timeunits_declaration ] { non_port_module_item } endmodule [ : module_identifier ]
    /// interface_declaration ::= interface_ansi_header [ timeunits_declaration ] { non_port_interface_item } endinterface [ : interface_identifier ]
    /// program_declaration    ::= program_ansi_header [ timeunits_declaration ] { non_port_program_item } endprogram [ : program_identifier ]

    /// module_ansi_header    ::= { attribute_instance } module_keyword [ lifetime ] module_identifier <{ package_import_declaration } [ parameter_port_list ] [ list_of_port_declarations ];>
    /// interface_ansi_header ::= { attribute_instance } interface [ lifetime ] interface_identifier <{ package_import_declaration } [ parameter_port_list ] [ list_of_port_declarations ];>
    /// program_ansi_header   ::= { attribute_instance } program [ lifetime ] program_identifier <{ package_import_declaration } [ parameter_port_list ] [ list_of_port_declarations ] ;>
    /// <> is handeld in InstanceBodySymbol 
    void handle(const slang::ast::InstanceSymbol& t) {
        
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
        write("end" + newSymbol);
    }

    /// ansi_port_declaration ::=[ net_port_header  ] port_identifier { unpacked_dimension } [ = constant_expression ]
    ///                          | [ variable_port_header ] port_identifier { variable_dimension } [ = constant_expression ]
    void handle(const slang::ast::PortSymbol& t) {
        // net_port_header      ::= [ port_direction ] net_port_type
        // variable_port_header ::= [ port_direction ] variable_port_type
        writeDirection(t.direction);

        if(t.internalSymbol){
            t.internalSymbol->visit(*this);
        }
        else{
            write(t.getType().toString());

        }
        // write port_identifier
        write(t.name);
        if (!t.isNetPort()){
            //variable_dimension ::= unsized_dimension | unpacked_dimension | associative_dimension | queue_dimension
            //TODODODODODODOD samen met unpacked 
        }

        if (t.getInternalExpr())
            t.getInternalExpr()->visit(*this);
        
        if (t.getInitializer()){
            write("=", false);
            t.getInitializer()->visit(*this);
        }

    }
    /// ansi_port_declaration ::=[ interface_port_header ] port_identifier { unpacked_dimension } [ = constant_expression ]
    void handle(const slang::ast::InterfacePortSymbol& t) {
        // interface_port_header ::= interface_identifier [ . modport_identifier]
        if(t.interfaceDef){
            write(t.interfaceDef->name);
        } else{
            write("interface");
        }

        if (t.modport != "" ){
            write(".",false);
            write(t.modport,false);
        }

        // write port_identifier
        write(t.name);

        //TODO:[ = constant_expression ]       
    }

    /// net_port_type ::= [ net_type ] data_type_or_implicit 
    void handle(const slang::ast::NetSymbol& t){
        //TODO dewe lijst afwerken , betere manier vinder
        switch(t.netType.netKind){
            case(NetType::NetKind::Wire):
                write("wire");
                break;
           case(NetType::NetKind::Interconnect):
                write("interconnect");
                break;
            case(NetType::NetKind::Supply0):
                write("supply0");
                break;
            case(NetType::NetKind::Supply1):
                write("supply1");
                break;
            case(NetType::NetKind::Tri0):
                write("tri0");
                break;
            case(NetType::NetKind::Tri1):
                write("tri1");
                break;
            case(NetType::NetKind::Tri):
                write("tri");
                break;
        }
        write(t.getType().toString());
    }

    /// variable_port_type ::= var_data_type
    /// var_data_type      ::= data_type | var data_type_or_implicit
    void handle(const slang::ast::VariableSymbol& t){
            write("var");
            write(t.getType().toString());
    }
    

    void handle(const slang::ast::MultiPortSymbol& t) {
        if (t.isNullPort) {
            return visitDefault(t);
        }

        writeDirection(t.direction);

        write(t.getType().toString());
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
    /// list_of_param_assignments ::= param_assignment { , param_assignment }  always with lenght 1 ??
    /// param_assignment ::= parameter_identifier { unpacked_dimension } [ = constant_param_expression ]
    void handle(const slang::ast::ParameterSymbol& t) {
        // parameter|localparam
        if (t.isLocalParam()){
            write(std::string_view("localparam"));
        }else {
            write(std::string_view("parameter"));
        }
        //data_type_or_implicit
        write(lowerFirstLetter(t.getType().toString()));
        //list_of_param_assignments->param_assignment->parameter_identifier
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

    ///package_import_item ::= package_identifier :: identifier
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
    // modport declartion with multiple items get automaticly splitted in multiple separete modport declartions
    void handle(const ModportSymbol& t) {
        write("modport");
        //modport_item ::= modport_identifier ( modport_ports_declaration { , modport_ports_declaration } )
        write(t.name);
        write("(");
        visitDefault(t);
        write(")");
        write(";");
    }

    // modport_ports_declaration ::= { attribute_instance } modport_simple_ports_declaration
    // modport_simple_ports_declaration ::= port_direction modport_simple_port { , modport_simple_port}
    // 
    void handle(const ModportPortSymbol& t) {
        writeAttributeInstances(t);
        writeDirection(t.direction);
        write(t.name);
    }

    void handle(const NamedValueExpression& t){
        write(t.symbol.name, false);
    }

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
            remainingMember = ((Symbol*) t.getParameters().back())->getNextSibling();
            write(")");
        }
 
        // list_of_port_declarations2 ::=( [ { attribute_instance} ansi_port_declaration { , { attribute_instance} ansi_port_declaration } ] )
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
            remainingMember =  t.getPortList().back()->getNextSibling();
            write(")");
        }

        write(";\n", false);

        //return if there are no remaining members
        while(remainingMember){
            if (remainingMember->kind != SymbolKind::Net ){
                remainingMember->visit(*this);
            }

            remainingMember = remainingMember->getNextSibling();
        }
        // add a tab to all folowing code
        indentation_level -= 1;
    }

    void handle(const slang::ast::IntegerLiteral& t) { write(t.getValue().toString(), false); }

    void handle(const slang::ast::ElementSelectExpression& t){
        write("[",false);
        t.selector().visit(*this);
        write("]",false);
    }

    std::string lowerFirstLetter(std::string_view string) {
        if (string == "")
            return "";
        // TODO: een beter manier vinden om dit te doen
        std::string new_string = std::string(string);
        new_string[0] = (char)tolower(new_string[0]);
        return new_string;
    }

private:
    std::string buffer;
    std::list<std::string> writeNextBuffer;
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

    void write(std::string_view string, bool add_spacer = true) {
        // check if there is a $ sign in the string and add its content to the write next buffer
        // the $ is generated by the typewriter and repersents a jump ex: int$[] identifier -> int identifier[]
        int dollarLocation = string.find("$");
        bool writeNextIsEmpty = writeNextBuffer.empty();
        if (dollarLocation != -1){
            std::string nextStr = std::string(string.substr(dollarLocation+1));
            writeNextBuffer.push_back(nextStr);
            string = string.substr(0,dollarLocation);
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

        if (!writeNextIsEmpty){
            std::string element = writeNextBuffer.front();
            writeNextBuffer.pop_front();
            write(element,false);
        }

    }

    //#test schrijven
    // TODOO snappen waarom dat dit zo sketch is
    void writeStatementBlockSymbol(const StatementBlockSymbol& t) {
        // Represents a sequential or parallel block statement.
        // write(lowerFirstLetter(toString(t.defaultLifetime)));
        write(t.name, false);
    }

    void writeAttributeInstances(const Symbol& t){
        auto attributes = compilation.getAttributes(t);
        if (!attributes.empty()){
            write("(*");
            for(auto attrib: attributes){
                attrib->visit(*this);
                if (attrib != attributes.back())
                    write(",", false);
            write("*) ");

        }
    }}

    void writeTimeUnitsDeclaration(const std::optional<TimeScale> t){
        if (t.has_value()){
            write("timeunit");
            write(t.value().toString());
            write(";");
        }

    }

    void writeDirection(ArgumentDirection direction){
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

};

} // namespace slang::ast