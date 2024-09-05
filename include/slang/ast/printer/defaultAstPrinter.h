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
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/NetType.h"
#include "slang/ast/types/Type.h"
#include "slang/util/LanguageVersion.h"
#include "slang/util/Util.h"

namespace slang::ast {

template<typename T>
concept IsFunc = requires(T t) {
    // selects SubroutineSymbol, MethodPrototypeSymbol
    t.subroutineKind;
};

/// Provides support for printing a ast back to source code.
class AstPrinter : public ASTVisitor<AstPrinter, true, true, true> {
public:
    AstPrinter(slang::ast::Compilation& compilation) : compilation(compilation){};

    /// @return a view of the internal text buffer.
    std::string_view str() const { return buffer; }

    void handle(const InvalidStatement& t);

    // wait_statement ::= wait ( expression ) statement_or_null
    void handle(const WaitStatement& t);

    // wait_statement ::= wait fork;
    void handle(const WaitForkStatement& t);

    // wait_statement ::= wait_order ( hierarchical_identifier { , hierarchical_identifier } ) action_block
    void handle(const WaitOrderStatement& t);

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

    // void handle(const BinaryAssertionExpr& t);
    //  blocking_assignment    ::= variable_lvalue = delay_or_event_control expression |
    //                             variable_lvalue assignment_operator expression
    //  nonblocking_assignment ::= variable_lvalue <= [ delay_or_event_control ] expression
    void handle(const AssignmentExpression& t);

    void handle(const UnaryExpression& t);

    void handle(const BinaryExpression& t);

    // subroutine_call_statement ::=subroutine_call ;
    // subroutine_call ::= tf_call | system_tf_call | method_call | [ std:: ] randomize_call
    //  ps_or_hierarchical_tf_identifier { attribute_instance } [ ( list_of_arguments ) ]
    //  system_tf_call ::= system_tf_identifier [ ( list_of_arguments ) ]
    void handle(const CallExpression& t);

    void handle(const NamedValueExpression& t);

    void handle(const ArbitrarySymbolExpression& t);

    void handle(const UnbasedUnsizedIntegerLiteral& t);

    void handle(const UnboundedLiteral& t);

    void handle(const IntegerLiteral& t);

    void handle(const ElementSelectExpression& t);

    void handle(const DistExpression& t);

    // inside_expression ::= expression inside { open_range_list }
    void handle(const InsideExpression& t);

    // value_range ::=expression| [ expression : expression ]
    void handle(const RangeSelectExpression& t);

    // class_new ::=[ class_scope ] new [ ( list_of_arguments ) ]
    void handle(const NewClassExpression& t);

    // class_new ::=[ class_scope ] new [ ( list_of_arguments ) ]
    void handle(const MemberAccessExpression& t);

    void handle(const SimpleAssignmentPatternExpression& t);

    void handle(const BinSelectWithFilterExpr& t);

    void handle(const BinaryBinsSelectExpr& t);

    // select_condition ::= binsof ( bins_expression ) [ intersect { covergroup_range_list } ]
    void handle(const ConditionBinsSelectExpr& t);

    void handle(const UnaryBinsSelectExpr& t);

    // void handle(const AssertionInstanceExpression& t);

    // void handle(const SimpleAssertionExpr& t);

    void handle(const StringLiteral& t);

    void handle(const RealLiteral& t);

    // event_control::= @ ( event_expression )
    // event_expression ::=[ edge_identifier ] expression [ iff expression ]
    void handle(const SignalEventControl& t);

    void handle(const ImplicitEventControl& t);

    // type_declaration ::= typedef data_type type_identifier { variable_dimension } ;
    // TODO: formating type_str
    void handle(const TypeAliasType& t);

    void handle(const ClassType& t);

    // covergroup_declaration ::= covergroup covergroup_identifier [ ( [ tf_port_list ] ) ] [
    // coverage_event ] ;{ coverage_spec_or_option } endgroup [ : covergroup_identifier ]
    void handle(const CovergroupType& t);

    void handle(const CoverageOptionSetter& t);

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

    void handle(const EventListControl& t);

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

    /// ansi_port_declaration ::=[ net_port_header  ] port_identifier { unpacked_dimension } [ =
    /// constant_expression ]
    ///                          | [ variable_port_header ] port_identifier { variable_dimension } [
    ///                          = constant_expression ]
    void handle(const slang::ast::PortSymbol& t);

    ///(non ansi) port ::=[ port_expression ] | . port_identifier ( [ port_expression ] )
    /// port_reference ::= port_identifier constant_select
    void handleNonAnsiPort(const slang::ast::PortSymbol& t);

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

    // udp_declaration ::= udp_ansi_declaration udp_body endprimitive [ : udp_identifier ]
    void handle(const PrimitiveSymbol& t);

    // config_declaration ::= config config_identifier ; { local_parameter_declaration ;
    // }design_statement { config_rule_statement } endconfig [ : config_identifier ]
    void handle(const ConfigBlockSymbol& t);

    // specify_block ::= specify { specify_item } endspecify
    void handle(const SpecifyBlockSymbol& t);

    // specparam_declaration ::= specparam [ packed_dimension ] list_of_specparam_assignments ;
    void handle(const SpecparamSymbol& t);

    // path_declaration ::=simple_path_declaration ;| edge_sensitive_path_declaration ; |
    // state_dependent_path_declaration;
    void handle(const TimingPathSymbol& t);

    // dient voor SubroutineSymbol, MethodPrototypeSymbol
    // method_prototype ::= task_prototype | function_prototype
    // function_prototype ::= function data_type_or_void function_identifier [ ( [ tf_port_list ] )
    // ] task_prototype ::= task task_identifier [ ( [ tf_port_list ] ) ]
    template<IsFunc T>
    void handle(const T& t);

    void handle(const FormalArgumentSymbol& t);

    void handle(const UninstantiatedDefSymbol& t);

    void handle(const CompilationUnitSymbol& t);

    // class_property ::= { property_qualifier } data_declaration
    void handle(const ClassPropertySymbol& t);

    // checker_declaration ::= checker checker_identifier [ ( [ checker_port_list ] ) ] ; { {
    // attribute_instance } checker_or_generate_item } endchecker [ : checker_identifier ]
    void handle(const CheckerSymbol& t);

    void handle(const CheckerInstanceSymbol& t);

    // checker_declaration  { { attribute_instance } checker_or_generate_item } these values get inserted in CheckerSymbol 
    void handle(const CheckerInstanceBodySymbol& t, const std::map<std::string, std::string> &connectionMapping = std::map<std::string, std::string>());

    // clocking_declaration ::= [ default ] clocking [ clocking_identifier ] clocking_event ;{
    // clocking_item }endclocking [ : clocking_identifier ]
    void handle(const ClockingBlockSymbol& t);

    /// { package_import_declaration } [ parameter_port_list ] [ list_of_port_declarations ];
    void handle(const InstanceBodySymbol& t);

    void handle(const GenericClassDefSymbol& t);

    // constraint_declaration ::= [ static ] constraint constraint_identifier constraint_block
    void handle(const ConstraintBlockSymbol& t);

    // production ::= [ data_type_or_void ] production_identifier [ ( tf_port_list ) ] : rs_rule { |
    // rs_rule } ;
    void handle(const RandSeqProductionSymbol& t);

    void handle(const RandSequenceStatement& t);

    void handle(const RandSeqProductionSymbol::ProdBase& t);

    void handle(const RandSeqProductionSymbol::CaseItem& t);

    void handle(std::span<const RandSeqProductionSymbol::Rule> t);

    void handle(const ConstraintList& t);

    void handle(const CoverpointSymbol& t);

    void handle(const CovergroupBodySymbol& t);

    // cover_cross ::=[ cross_identifier : ] cross list_of_cross_items [ iff ( expression ) ]
    // cross_body
    void handle(const CoverCrossSymbol& t);

    //
    void handle(const CoverageBinSymbol& t);

    // cross_body ::= { { cross_body_item ; } }
    void handle(const CoverCrossBodySymbol& t);

    //severity_system_task ::=  $fatal [ ( finish_number [, list_of_arguments ] ) ] ;
    //                      | $error [ ( [ list_of_arguments ] ) ] ;
    //                      | $warning [ ( [ list_of_arguments ] ) ] ;
    //                      | $info [ ( [ list_of_arguments ] ) ] ;
    void handle(const ElabSystemTaskSymbol& t);

    void visitTransList(std::span<const CoverageBinSymbol::TransRangeList> set);

    void visitTransSet(std::span<const CoverageBinSymbol::TransSet> list);

    void handle(const ExpressionConstraint& t);

    void handle(const ImplicationConstraint& t);

    void handle(const SolveBeforeConstraint& t);

    void handle(const ConditionalConstraint& t);

    void handle(const ForeachConstraint& t);

    void handle(const DisableSoftConstraint& t);

private:
    std::string buffer;
    std::string* tempBuffer;
    std::list<std::string> writeNextBuffer;

    // used to make sure the internalSymbol of ansi ports aren't written as a member of a
    // instanceBody, to make sure the direction of ansi ports is known.
    std::map<const slang::ast::Symbol*, ArgumentDirection> internalSymbols;


    // the type in the ast is not the type defined by the type alias, this map is used to convert
    // the type back to the type alias type
    std::map<std::string, std::string> typeConversions;

    // buffer for code in a statementblock that needs to be appended in the next proceduralBlock
    std::string blockBuffer;

    Compilation& compilation;

    bool useTempBuffer = false;
    bool inEventList = false;
    bool isFrontEventList = false;
    bool isBackEventList = false;

    // used to get parent symbol while you are in a expression
    const Symbol* currSymbol;

    // used to detect if a visit has changed the buffer
    int changedBuffer = 0;

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
        // removes class identifiers because they are unwanted most of the time
        // ex: enum{red=32'sd0,green=32'sd1,blue=32'sd2}C3::e
        std::regex reg2("(?=}).*::.*");
        type = std::regex_replace(type, reg, "}");
        type = std::regex_replace(type, reg2, "}");

        int dot_loc = type.rfind(".");
        if (typeConversions.count(type.substr(0, dot_loc)))
            return typeConversions[type.substr(0, dot_loc)];
        return type;
    }

    // this function is used when visiting the members of a scope, in this case not every element has to be ended with the divider.
    // To prevent this behavouir element which already contain a newline are skipped  if newline is true
    void visitMembers(const Symbol* member, const std::string& div = ",", bool newline = true) {
        std::string endChar = newline?"\n":std::string(div);
        while (member) {
            int currentBuffer = changedBuffer;
            member->visit(*this);
            std::string* writeBuffer = (useTempBuffer) ? (tempBuffer) : (&this->buffer);
            
            bool needsDivider = endChar != (*writeBuffer).substr((*writeBuffer).length() - endChar.length(), (*writeBuffer).length() - endChar.length());
            if (*writeBuffer != "" && needsDivider && (changedBuffer != currentBuffer)) {
                write(std::string(div) + (newline?"\n":""),false);
            }
            member = member->getNextSibling();
        }
    }

    template<typename T>
    void visitMembers(std::span<const T* const> t, const std::string& div = ",",
                      bool newline = false) {
        for (auto item : t) {
            int currentBuffer = changedBuffer;
            item->visit(*this);
            if (item != t.back() && changedBuffer != currentBuffer)
                write(div, false);
            std::string* writeBuffer = (useTempBuffer) ? (tempBuffer) : (&this->buffer);
            if (*writeBuffer != "" && newline &&("\n" != (*writeBuffer).substr((*writeBuffer).length() - 1, (*writeBuffer).length() - 1)))
                write("\n", false);
        }
    }

    template<typename T>
    void visitMembers(std::span<const T> t, const std::string& divider = ",",
                      bool newline = false) {
        for (auto item : t) {
            int currentBuffer = changedBuffer;
            handle(item);

            if (&item != &t.back() && changedBuffer != currentBuffer)
                write(divider, false);

            std::string* writeBuffer = (useTempBuffer) ? (tempBuffer) : (&this->buffer);
            if (*writeBuffer != "" && newline &&("\n" != (*writeBuffer).substr((*writeBuffer).length() - 1, (*writeBuffer).length() - 1)))
                write("\n", false);
        }
    }

    void write(std::string_view string, bool add_spacer = true, bool use_dollar = false) {
        if (string != "")
            changedBuffer++;
        // check if there is a $ sign in the string and add its content to the writeNext buffer
        // the $ is generated by the typewriter and represents a jump ex: int$[] identifier -> int
        // identifier[]
        int dollarLocation = string.find("$");
        std::string* writeBuffer = (useTempBuffer) ? (tempBuffer) : (&this->buffer);

        bool writeNextIsEmpty = writeNextBuffer.empty();
        if (dollarLocation != -1 && use_dollar) {
            std::string nextStr = std::string(string.substr(dollarLocation + 1));
            writeNextBuffer.push_back(nextStr);
            string = string.substr(0, dollarLocation);
        }

        if ((*writeBuffer).back() == '\n') {
            // solves the indentation in new lines
            std::string depth_string = std::string(indentation_level * indentation_multiplier, ' ');
            (*writeBuffer).append(depth_string);
        }

        // buffer == "" is added to ensure the first char of the program does not have a space
        // infront of it
        else if (add_spacer && (*writeBuffer) != "") {
            (*writeBuffer).append(" ");
        }
        (*writeBuffer).append(std::string(string));

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
            case (BinaryOperator::Divide):
                write("/", false);
                break;
            case (BinaryOperator::Mod):
                write("%", false);
                break;
            case (BinaryOperator::BinaryAnd):
                write("&", false);
                break;
            case (BinaryOperator::BinaryOr):
                write("|", false);
                break;
            case (BinaryOperator::BinaryXor):
                write("^", false);
                break;
            case (BinaryOperator::BinaryXnor):
                write("^~", false);
                break;
            case (BinaryOperator::Equality):
                write("==", false);
                break;
            case (BinaryOperator::Inequality):
                write("!=", false);
                break;
            case (BinaryOperator::CaseEquality):
                write("===", false);
                break;
            case (BinaryOperator::CaseInequality):
                write("!==", false);
                break;
            case (BinaryOperator::GreaterThanEqual):
                write(">=", false);
                break;
            case (BinaryOperator::GreaterThan):
                write(">", false);
                break;
            case (BinaryOperator::LessThanEqual):
                write("<=", false);
                break;
            case (BinaryOperator::LessThan):
                write("<", false);
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
            case (BinaryOperator::ArithmeticShiftLeft):
                write("<<<", false);
                break;
            case (BinaryOperator::ArithmeticShiftRight):
                write(">>>", false);
                break;
            case (BinaryOperator::LogicalShiftLeft):
                write(">>", false);
                break;
            case (BinaryOperator::LogicalShiftRight):
                write("<<", false);
                break;
            case (BinaryOperator::Power):
                write("**", false);
                break;
           case (BinaryOperator::WildcardEquality):
                write("==", false);
                break;
            case (BinaryOperator::WildcardInequality):
                write("!=?"), false;
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
            case (UnaryOperator::LogicalNot):
                write("!", false, true);
                break;
            case (UnaryOperator::BitwiseAnd):
                write("&", false, true);
                break;
            case (UnaryOperator::BitwiseNand):
                write("~&", false, true);
                break;
            case (UnaryOperator::BitwiseOr):
                write("|", false, true);
                break;
            case (UnaryOperator::BitwiseNor):
                write("~|", false, true);
                break;
            case (UnaryOperator::BitwiseNot):
                write("~", false, true);
                break;
            case (UnaryOperator::BitwiseXor):
                write("^", false, true);
                break;
            case (UnaryOperator::BitwiseXnor):
                write("^", false, true);
                break;
            case (UnaryOperator::Minus):
                write("-", false, true);
                break;
            case (UnaryOperator::Plus):
                write("+", false, true);
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

    void write(BinaryAssertionOperator op) {
        switch (op) {
            case (BinaryAssertionOperator::And):
                write("and", false);
                break;
            case (BinaryAssertionOperator::Iff):
                write("iff", false);
                break;
            case (BinaryAssertionOperator::Implies):
                write("implies", false);
                break;
            case (BinaryAssertionOperator::Intersect):
                write("intersect", false);
                break;
            case (BinaryAssertionOperator::OverlappedImplication):
                write("|->");
                break;
            case (BinaryAssertionOperator::OverlappedFollowedBy):
                write("#-#", false);
                break;
            case (BinaryAssertionOperator::Or):
                write("or", false);
                break;
            case (BinaryAssertionOperator::NonOverlappedFollowedBy):
                write("#=#", false);
                break;
            case (BinaryAssertionOperator::NonOverlappedImplication):
                write("|=>");
                break;
            case (BinaryAssertionOperator::SUntil):
                write("s_until");
                break;
            case (BinaryAssertionOperator::SUntilWith):
                write("s_until_with");
                break;
            case (BinaryAssertionOperator::Throughout):
                write("throughout");
                break;
             case (BinaryAssertionOperator::Until):
                write("until");
                break;
            case (BinaryAssertionOperator::UntilWith):
                write("until_with");
                break;
            case (BinaryAssertionOperator::Within):
                write("within");
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    void write(CoverageBinSymbol::BinKind kind) {
        switch (kind) {
            case (CoverageBinSymbol::BinKind::Bins):
                write("bins");
                break;
            case (CoverageBinSymbol::BinKind::IllegalBins):
                write("illegal_bins");
                break;
            case (CoverageBinSymbol::BinKind::IgnoreBins):
                write("ignore_bins");
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    void write(CoverageBinSymbol::TransRangeList::RepeatKind kind) {
        switch (kind) {
            case (CoverageBinSymbol::TransRangeList::RepeatKind::None):
                break;
            case (CoverageBinSymbol::TransRangeList::RepeatKind::Consecutive):
                write("*");
                break;
            case (CoverageBinSymbol::TransRangeList::RepeatKind::Nonconsecutive):
                write("=");
                break;
            case (CoverageBinSymbol::TransRangeList::RepeatKind::GoTo):
                write("->");
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }
    
    void write(ValueRangeKind kind) {
        switch (kind) {
            case (ValueRangeKind::Simple):
                write(":");
                break;
            case (ValueRangeKind::AbsoluteTolerance):
                write("+/-");
                break;
            case (ValueRangeKind::RelativeTolerance):
                write("+%-");
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }


    void writeName(const Symbol& t, bool add_spacer = true) {
        write(getRealName(t, currSymbol), add_spacer);
    }

    // attempt to get the real hierachical name of an object ex:e.a instead of $root.m.e.a
    // It does this by trying to find the scope in which both the caller and the actual item are visible
    std::string getRealName(const Symbol& item, const Symbol* caller) {
        // caller is often this.currSymnol which can be null
        if (!caller)
            return std::string(item.name);

        // loop through the parents of the item until the scope of the parent contains the other
        // symbol
        auto parent = item.getParentScope();
        while (!Lookup::isVisibleFrom(*caller, *parent)) {
            auto& parent_symbol = parent->asSymbol();
            parent = parent_symbol.getParentScope();
        }

        if (parent) {
            auto& parent_symbol = parent->asSymbol();

            std::string parent_path_name = "";
            std::string item_path_name = "";
            auto grandparent = parent_symbol.getParentScope();

            if (grandparent) {

                grandparent->asSymbol().getHierarchicalPath(parent_path_name);
                parent_path_name += ".";
                item.getHierarchicalPath(item_path_name);

                if (parent_path_name.length()<item_path_name.length()&& item_path_name.find(parent_path_name) != -1) {
                    item_path_name.replace(item_path_name.find(parent_path_name),
                                           parent_path_name.length(), "");
                    return item_path_name;
                }
            }
        }

        // incase item / caller is a class element is check if it needs extra identification ex:super
       if(item.getParentScope() && (*caller).getParentScope()){
            std::pair<const ClassType*, bool> itemClassPair=  Lookup::getContainingClass(*item.getParentScope());
            //check if the caller is a member of the same class
            std::pair<const ClassType*, bool> callerClassPair=  Lookup::getContainingClass((*(*caller).getParentScope()));

            if(itemClassPair.first && callerClassPair.first){
                // if they are the same class there is no problem
                if (itemClassPair.first == callerClassPair.first)
                    return std::string(item.name);

                if (callerClassPair.first->getBaseClass() == itemClassPair.first )
                    return "super." + std::string(item.name);
                else{
                    return std::string(itemClassPair.first->name) +"::" + std::string(item.name);
                }
        }
        }
        return std::string(item.name);
    }


    std::string lowerFirstLetter(std::string_view string) {
        if (string == "")
            return "";
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
};

} // namespace slang::ast
