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
#include <map>
#include <regex>
#include <set>
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

    /// Sets whether to include trivia when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    AstPrinter& setIncludeTrivia(bool include);

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
    void handle(const InvalidStatement& t);

    // wait_statement ::= wait ( expression ) statement_or_null
    void handle(const WaitStatement& t);

    // wait_statement ::= wait fork;
    void handle(const WaitForkStatement& t);

    // wait_statement ::= wait_order ( hierarchical_identifier { , hierarchical_identifier } )
    // action_block
    void handle(const WaitOrderStatement& t);
    // #test schrijven
    void handle(const InvalidAssertionExpr& t);

    // hierarchical_identifier ::= [ $root . ] { identifier constant_bit_select . } identifier
    void handle(const HierarchicalValueExpression& t);

    // net_lvalue ::={ net_lvalue { , net_lvalue } } (this is used in other instances asswel)
    void handle(const ConcatenationExpression& t);

    void handle(const NewArrayExpression& t);

    // mintypmax_expression ::= expression | expression : expression : expression
    void handle(const MinTypMaxExpression& t);

    // value_range ::= expression | [ expression : expression ]
    // TODO uitzoeken waarvoor die valuerange kind dient
    void handle(const ValueRangeExpression& t);

   //void handle(const BinaryAssertionExpr& t);

    // blocking_assignment    ::= variable_lvalue = delay_or_event_control expression |
    //                            variable_lvalue assignment_operator expression
    // nonblocking_assignment ::= variable_lvalue <= [ delay_or_event_control ] expression
    void handle(const AssignmentExpression& t);

    void handle(const UnaryExpression& t);

    void handle(const BinaryExpression& t);

    // subroutine_call_statement ::=subroutine_call ;
    // subroutine_call ::= tf_call | system_tf_call | method_call | [ std:: ] randomize_call
    //  ps_or_hierarchical_tf_identifier { attribute_instance } [ ( list_of_arguments ) ]
    //  system_tf_call ::= system_tf_identifier [ ( list_of_arguments ) ]
    void handle(const CallExpression& t);

    void handle(const StringLiteral& t);

    void handle(const RealLiteral& t);

    // event_control::= @ ( event_expression )
    // event_expression ::=[ edge_identifier ] expression [ iff expression ]
    void handle(const SignalEventControl& t);

    void handle(const ImplicitEventControl& t);

    // type_declaration ::= typedef data_type type_identifier { variable_dimension } ;
    // TODO: formating type_str
    void handle(const TypeAliasType& t);

    //
    void handle(const EmptyStatement& t);

    //
    void handle(const StatementList& t);

    //
    void handle(const VariableDeclStatement& t);

    // disable_statement ::= disable fork ;
    void handle(const DisableForkStatement& t);

    // disable_statement ::= disable hierarchical_block_identifier ;
    void handle(const DisableStatement& t);

    // jump_statement ::=break ;
    void handle(const BreakStatement& t);

    // jump_statement ::=continue ;
    void handle(const ContinueStatement& t);

    void handle(const ExpressionStatement& t);

    // loop_statement ::= repeat ( expression ) statement_or_null
    // statement_or_null ::=statement| { attribute_instance } ;
    // statement ::= [ block_identifier : ] { attribute_instance } statement_item
    void handle(const RepeatLoopStatement& t);

    // loop_statement ::= forever statement_or_null
    void handle(const ForeverLoopStatement& t);

    // loop_statement ::= foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] )
    // statement
    void handle(const ForeachLoopStatement& t);

    // loop_statement ::= while ( expression ) statement_or_null
    void handle(const WhileLoopStatement& t);

    // for ( [ for_initialization ] ; [ expression ] ; [ for_step ] ) statement_or_null
    void handle(const ForLoopStatement& t);

    // conditional_statement ::= [ unique_priority ] if ( cond_predicate ) statement_or_null {else
    // if ( cond_predicate ) statement_or_null } [ else statement_or_null ]
    void handle(const ConditionalStatement& t);

    // case_statement ::= [ unique_priority ] case_keyword ( case_expression ) case_item {
    // case_item} endcase
    //                  | [ unique_priority ] case ( case_expression ) inside case_inside_item {
    //                  case_inside_item } endcase
    void handle(const CaseStatement& t);

    void handle(const BlockStatement& t);

    // immediate_assertion_statement        ::= simple_immediate_assertion_statement |
    // deferred_immediate_assertion_statement simple_immediate_assertion_statement ::=
    // simple_immediate_assert_statement simple_immediate_assert_statement    ::= assert (
    // expression ) action_block action_block ::=statement_or_null | [ statement ] else
    // statement_or_null 
    void handle(const ImmediateAssertionStatement& t);

    // concurrent_assertion_statement ::=assert_property_statement| assume_property_statement
    void handle(const ConcurrentAssertionStatement& t);

    // case_statement ::= | [ unique_priority ] case_keyword (case_expression )matches
    //                       case_pattern_item { case_pattern_item } endcase
    void handle(const PatternCaseStatement& t);

    // pattern ::= tagged member_identifier [ pattern ]
    void handle(const TaggedPattern& t);

    // pattern ::=. variable_identifier
    void handle(const VariablePattern& t);
    // pattern ::= .*
    void handle(const WildcardPattern& t);

    // assignment_pattern ::= '{ expression { , expression } }
    void handle(const StructurePattern& t);

    void handle(const GenvarSymbol& t);

    void handle(const GenerateBlockSymbol& t);

    // loop_generate_construct ::= for ( genvar_initialization ; genvar_expression ;
    // genvar_iteration ) generate_block
    void handle(const GenerateBlockArraySymbol& t);

    void handle(const AttributeSymbol& t);

    void handle(const StatementBlockSymbol& t);

    // property_declaration ::= property property_identifier [ ( [ property_port_list ] ) ] ;{
    // assertion_variable_declaration }property_spec [ ; ] endproperty
    void handle(const PropertySymbol& t);

    // property_port_item ::={ attribute_instance } [ local [ property_lvar_port_direction ] ]
    // property_formal_typeformal_port_identifier {variable_dimension} [ = property_actual_arg ]
    void handle(const AssertionPortSymbol& t);

    /*
    package_declaration ::=
            { attribute_instance } package [ lifetime ] package_identifier ;
            [ timeunits_declaration ] { { attribute_instance } package_item }
        endpackage [ : package_identifier ]
    */
    void handle(const PackageSymbol& t);

    // anonymous_program ::= program ; { anonymous_program_item } endprogram
    void handle(const AnonymousProgramSymbol& t);

    // ding zoals initial
    void handle(const ProceduralBlockSymbol& t);

    // continuous_assign ::= assign [ drive_strength ] [ delay3 ] list_of_net_assignments ;
    //                     | assign [ delay_control ] list_of_variable_assignments ;
    void handle(const ContinuousAssignSymbol& t);

    // delay_control ::= # delay_value | # ( mintypmax_expression )
    void handle(const DelayControl& t);

    void handle(const Delay3Control& t);

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
    void handle(const slang::ast::InstanceSymbol& t);

    /// ansi_port_declaration ::=[ net_port_header  ] port_identifier { unpacked_dimension } [ = constant_expression ]
    ///                          | [ variable_port_header ] port_identifier { variable_dimension } [ = constant_expression ]
    void handle(const slang::ast::PortSymbol& t);

    /// ansi_port_declaration ::=[ interface_port_header ] port_identifier { unpacked_dimension } [
    /// = constant_expression ]
    void handle(const slang::ast::InterfacePortSymbol& t);

    /// net_port_type ::= [ net_type ] data_type_or_implicit
    void handle(const slang::ast::NetSymbol& t);

    void handle(const slang::ast::ScalarType& t);

    /// variable_port_type ::= var_data_type
    /// var_data_type      ::= data_type | var data_type_or_implicit
    // data_declaration10 ::=  [ var ] [ lifetime ] data_type_or_implicit
    void handle(const slang::ast::VariableSymbol& t);

    void handle(const slang::ast::MultiPortSymbol& t);

    /// parameter_declaration ::= parameter data_type_or_implicit list_of_param_assignments
    /// local_parameter_declaration ::= localparam data_type_or_implicit list_of_param_assignments
    /// list_of_param_assignments ::= param_assignment { , param_assignment }  always with lenght 1
    /// ?? param_assignment ::= parameter_identifier { unpacked_dimension } [ =
    /// constant_param_expression ]
    void handle(const slang::ast::ParameterSymbol& t);

    // Represents a module, interface, or program definition
    void handle(const DefinitionSymbol& t);

    /// package_import_item ::= package_identifier :: identifier
    void handle(const ExplicitImportSymbol& t);

    // package_import_item ::= package_identifier :: *
    void handle(const WildcardImportSymbol& t);

    // modport_declaration ::= modport modport_item { , modport_item } ;
    // modport declartion with multiple items get automaticly splitted in multiple separete modport
    // declartions
    void handle(const ModportSymbol& t);

    // net_alias ::= alias net_lvalue = net_lvalue { = net_lvalue } ;
    void handle(const NetAliasSymbol& t);

    // modport_ports_declaration ::= { attribute_instance } modport_simple_ports_declaration
    // modport_simple_ports_declaration ::= port_direction modport_simple_port {
    // ,modport_simple_port}
    void handle(const ModportPortSymbol& t);

    // udp_output_declaration ::= { attribute_instance } output port_identifier
    // udp_input_declaration ::= { attribute_instance } input list_of_udp_port_identifiers
    void handle(const PrimitivePortSymbol& t);

    //udp_declaration ::= udp_ansi_declaration udp_body endprimitive [ : udp_identifier ]
    void handle(const PrimitiveSymbol& t);

    //config_declaration ::= config config_identifier ; { local_parameter_declaration ; }design_statement { config_rule_statement } endconfig [ : config_identifier ]
    void handle(const ConfigBlockSymbol& t);

    // specify_block ::= specify { specify_item } endspecify
    void handle(const SpecifyBlockSymbol& t);

    //specparam_declaration ::= specparam [ packed_dimension ] list_of_specparam_assignments ;
    void handle(const SpecparamSymbol& t);
    
    // path_declaration ::=simple_path_declaration ;| edge_sensitive_path_declaration ; | state_dependent_path_declaration;
    void handle(const TimingPathSymbol& t);
    
    // method_prototype ::= task_prototype | function_prototype
    void handle(const MethodPrototypeSymbol& t);

    void handle(const FormalArgumentSymbol& t);

    void handle(const NamedValueExpression& t);

    /// { package_import_declaration } [ parameter_port_list ] [ list_of_port_declarations ];
    void handle(const InstanceBodySymbol& t);

    void handle(const UnbasedUnsizedIntegerLiteral& t);

    void handle(const IntegerLiteral& t);

    void handle(const ElementSelectExpression& t);

    //void handle(const AssertionInstanceExpression& t);

    //void handle(const SimpleAssertionExpr& t);

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
    // used make sure the internalSymbol of ports aren't written as a member of a instanceBody
    std::set<const slang::ast::Symbol*> internalSymbols;
    // used to ensure interfaces, .. are only written fully  once
    std::set<const slang::ast::InstanceBodySymbol*> initializedInstances;
    // the type in the ast is not the type defined by the type alias, this map is used to convert
    // the type back to the type alias type
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
    std::string convertType(std::string type) {
        // check if type in type conversions
        // remove the name of the typealias to make it possible to compare them to typealias types
        // ex: type alieas union tagged{void Invalid;int Valid;}m3.u$1 (this is named VInt)
        //     getType(): union tagged{void Invalid;int Valid;}m3.VInt
        std::regex reg("}.*?(?= .\\S*?;)");
        type = std::regex_replace(type, reg, "}");

        int dot_loc = type.rfind(".");
        if (typeConversions.count(type.substr(0, dot_loc)))
            return typeConversions[type.substr(0, dot_loc)];
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

    void write(NetType::NetKind kind) {
        switch (kind) {
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
            case (BinaryOperator::Inequality):
                write("!=", false);
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
            case (BinaryOperator::LogicalAnd):
                write("&&", false);
                break;
            case (BinaryOperator::LogicalOr):
                write("||", false);
                break;
            case (BinaryOperator::LogicalEquivalence):
                write("||", false);
                break;
            case (BinaryOperator::BinaryOr):
                write("|", false);
                break;
            case (BinaryOperator::BinaryAnd):
                write("&", false);
                break;
            case (BinaryOperator::BinaryXnor):
                write("^~", false);
                break;
            case (BinaryOperator::BinaryXor):
                write("^", false);
                break;
            case (BinaryOperator::ArithmeticShiftLeft):
                write("<<<");
                break;
            case (BinaryOperator::ArithmeticShiftRight):
                write(">>>");
                break;
            case (BinaryOperator::LogicalShiftLeft):
                write(">>");
                break;
            case (BinaryOperator::LogicalShiftRight):
                write("<<");
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


    void write(PrimitivePortDirection direction) {
        switch (direction) {
            case (PrimitivePortDirection::In):
                write("input", false);
                break;
            case (PrimitivePortDirection::Out):
                write("output", false);
                break;
            case (PrimitivePortDirection::OutReg):
                write("output reg", false);
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }


    void write(AssertionKind assertion) {
        switch (assertion) {
            case (AssertionKind::Assert):
            case (AssertionKind::Assume):
                write(lowerFirstLetter(toString(assertion)));
                break;
            case (AssertionKind::CoverProperty):
            case (AssertionKind::CoverSequence):
                write("cover");
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

    void write(BinaryAssertionOperator op){
        switch (op) {
            case (BinaryAssertionOperator::And):
                write("and", false);
                break;
            case (BinaryAssertionOperator::Or):
                write("or", false);
                break;
            case (BinaryAssertionOperator::Implies):
                write("|->", false);
                break;
            case (BinaryAssertionOperator::Intersect):
                write("intersect", false);
                break;
            case (BinaryAssertionOperator::OverlappedImplication):
                write("|->");
                break;
            default:
                SLANG_UNREACHABLE;
        }

    }
};

} // namespace slang::ast
