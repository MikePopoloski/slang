//------------------------------------------------------------------------------
//! @file Pattern.h
//! @brief Support for printing patterns from the ast
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "slang/ast/printer/defaultAstPrinter.h"

namespace slang::ast {

// case_statement ::= | [ unique_priority ] case_keyword (case_expression )matches
//                       case_pattern_item { case_pattern_item } endcase
void AstPrinter::handle(const PatternCaseStatement& t) {
    if (t.check != UniquePriorityCheck::None) {
        const std::string_view priority = toString(t.check);
        write(lowerFirstLetter(priority));
    }

    // case_keyword
    write(t.condition);
    write("(");
    t.expr.visit(*this);
    write(") matches\n");
    ++indentation_level;

    // case_pattern_item ::= pattern [ &&& expression ] : statement_or_null
    for (const auto& item : t.items) {
        item.pattern.get()->visit(*this);
        if (item.filter) {
            write("&&&");
            item.filter->visit(*this);
        }
        write(":");
        // TODO for some reasong the PatternCaseStatement creates an extra
        // inner BlockStatement while only 1 expression is present. This
        // behaviour has changed over the past iterations. This is temporary
        // workaround since I don't know if the extra Statement Block is
        // intended
        if (item.stmt->kind == slang::ast::StatementKind::Block) {
          const auto innerStatement = reinterpret_cast<const slang::ast::BlockStatement*>(item.stmt.get());
          innerStatement->body.visit(*this);
        } else {
            item.stmt->visit(*this);
        }

        write("\n");
    }

    // case_item ::= | default [ : ] statement_or_null
    if (t.defaultCase) {
        write("default :");
        t.defaultCase->visit(*this);
        write("\n");
    }

    --indentation_level;
    write("endcase \n");
}

// pattern ::= tagged member_identifier [ pattern ]
void AstPrinter::handle(const TaggedPattern& t) {
    write("tagged");
    writeName(t.member);
    t.valuePattern->visit(*this);
}

// pattern ::=. variable_identifier
void AstPrinter::handle(const VariablePattern& t) {
    write(".");

    writeName(t.variable, false);
}

// pattern ::= .*
void AstPrinter::handle(const WildcardPattern& t) {
    write(".*");
    visitDefault(t);
}

// assignment_pattern ::= '{ expression { , expression } }
void AstPrinter::handle(const StructurePattern& t) {
    write("'{");
    for (const auto& field_pattern : t.patterns) {
        const int currentBuffer = changedBuffer;
        field_pattern.pattern->visit(*this);
        if (&field_pattern != &(t.patterns.back()) && changedBuffer != currentBuffer) {
            write(",");
        }
    }
    write("}");
}

} // namespace slang::ast
