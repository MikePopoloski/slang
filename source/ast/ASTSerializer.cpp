//------------------------------------------------------------------------------
// ASTSerializer.cpp
// Support for serializing an AST
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ASTSerializer.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/types/TypePrinter.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/CharInfo.h"
#include "slang/text/FormatBuffer.h"
#include "slang/text/Json.h"
#include "slang/text/SourceManager.h"

namespace slang::ast {

ASTSerializer::ASTSerializer(Compilation& compilation, JsonWriter& writer) :
    compilation(compilation), writer(writer) {
}

void ASTSerializer::serialize(const Symbol& symbol, bool inMembersArray) {
    symbol.visit(*this, inMembersArray);
}

void ASTSerializer::serialize(const Expression& expr) {
    expr.visit(*this);
}

void ASTSerializer::serialize(const Statement& statement) {
    statement.visit(*this);
}

void ASTSerializer::serialize(const TimingControl& timing) {
    timing.visit(*this);
}

void ASTSerializer::serialize(const Constraint& constraint) {
    constraint.visit(*this);
}

void ASTSerializer::serialize(const AssertionExpr& expr) {
    expr.visit(*this);
}

void ASTSerializer::serialize(const BinsSelectExpr& expr) {
    expr.visit(*this);
}

void ASTSerializer::serialize(const Pattern& pattern) {
    pattern.visit(*this);
}

void ASTSerializer::serialize(std::string_view value) {
    writer.writeValue(value);
}

void ASTSerializer::write(std::string_view name, std::string_view value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(std::string_view name, int64_t value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(std::string_view name, uint64_t value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(std::string_view name, double value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(std::string_view name, bool value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(std::string_view name, const std::string& value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(std::string_view name, const Symbol& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(std::string_view name, const ConstantValue& value) {
    writer.writeProperty(name);
    writer.writeValue(value.toString(SVInt::MAX_BITS, /* exactUnknowns */ true,
                                     /* useAssignmentPatterns */ true));
}

void ASTSerializer::write(std::string_view name, const Expression& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(std::string_view name, const Statement& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(std::string_view name, const TimingControl& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(std::string_view name, const Constraint& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(std::string_view name, const AssertionExpr& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(std::string_view name, const BinsSelectExpr& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(std::string_view name, const Pattern& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::writeLink(std::string_view name, const Symbol& value) {
    writer.writeProperty(name);

    std::string str;
    if (includeAddrs)
        str = std::to_string(uintptr_t(&value)) + " ";

    if (value.isType())
        str += value.as<Type>().toString();
    else
        str += std::string(value.name);

    writer.writeValue(str);
}

void ASTSerializer::startArray() {
    writer.startArray();
}

void ASTSerializer::startArray(std::string_view name) {
    writer.writeProperty(name);
    writer.startArray();
}

void ASTSerializer::endArray() {
    writer.endArray();
}

void ASTSerializer::startObject() {
    writer.startObject();
}

void ASTSerializer::endObject() {
    writer.endObject();
}

void ASTSerializer::writeProperty(std::string_view name) {
    writer.writeProperty(name);
}

template<typename T>
void ASTSerializer::visit(const T& elem, bool inMembersArray) {
    if constexpr (std::is_base_of_v<Expression, T> || std::is_base_of_v<Statement, T> ||
                  std::is_base_of_v<TimingControl, T> || std::is_base_of_v<Constraint, T> ||
                  std::is_base_of_v<AssertionExpr, T> || std::is_base_of_v<BinsSelectExpr, T> ||
                  std::is_base_of_v<Pattern, T>) {
        writer.startObject();
        if (auto sm = compilation.getSourceManager(); sm && includeSourceInfo) {
            SourceRange range;
            if constexpr (requires { elem.sourceRange; }) {
                range = elem.sourceRange;
            }
            else if (elem.syntax) {
                range = elem.syntax->sourceRange();
            }

            if (range.start() && range.end() && range.start() != SourceLocation::NoLocation &&
                range.end() != SourceLocation::NoLocation) {
                auto start = sm->getFullyExpandedLoc(range.start());
                auto end = sm->getFullyExpandedLoc(range.end());
                write("source_file_start", sm->getFileName(start));
                write("source_file_end", sm->getFileName(end));
                write("source_line_start", sm->getLineNumber(start));
                write("source_line_end", sm->getLineNumber(end));
                write("source_column_start", sm->getColumnNumber(start));
                write("source_column_end", sm->getColumnNumber(end));
            }
        }
    }
    if constexpr (std::is_base_of_v<Expression, T>) {
        write("kind", toString(elem.kind));
        write("type", *elem.type);
        auto attributes = compilation.getAttributes(elem);
        if (!attributes.empty()) {
            startArray("attributes");
            for (auto attr : attributes)
                serialize(*attr);
            endArray();
        }

        if constexpr (!std::is_same_v<Expression, T>) {
            elem.serializeTo(*this);
        }

        if (tryConstantFold) {
            ASTContext ctx(compilation.getRoot(), LookupLocation::max);
            ConstantValue constant = ctx.tryEval(elem);
            if (constant)
                write("constant", constant);
        }
        else if (elem.getConstant()) {
            write("constant", *elem.getConstant());
        }

        writer.endObject();
    }
    else if constexpr (std::is_base_of_v<Statement, T>) {
        write("kind", toString(elem.kind));

        auto attributes = compilation.getAttributes(elem);
        if (!attributes.empty()) {
            startArray("attributes");
            for (auto attr : attributes)
                serialize(*attr);
            endArray();
        }

        if constexpr (!std::is_same_v<Statement, T>) {
            elem.serializeTo(*this);
        }

        writer.endObject();
    }
    else if constexpr (std::is_base_of_v<TimingControl, T> || std::is_base_of_v<Constraint, T> ||
                       std::is_base_of_v<AssertionExpr, T> ||
                       std::is_base_of_v<BinsSelectExpr, T> || std::is_base_of_v<Pattern, T>) {
        write("kind", toString(elem.kind));
        if constexpr (!std::is_same_v<TimingControl, T> && !std::is_same_v<Constraint, T> &&
                      !std::is_same_v<AssertionExpr, T> && !std::is_same_v<BinsSelectExpr, T> &&
                      !std::is_same_v<Pattern, T>) {
            elem.serializeTo(*this);
        }
        writer.endObject();
    }
    else {
        if constexpr (std::is_base_of_v<Type, T>) {
            auto printType = [&] {
                TypePrinter printer;
                printer.options.skipTypeDefs = true;
                if (includeAddrs) {
                    printer.options.typedefsAsLinks = true;
                    printer.options.enumsAsLinks = true;
                }

                printer.append(elem);
                return printer.toString();
            };

            // If we're not including detailed type info, we can just write the type name,
            // unless this a type alias, class, or covergroup. Otherwise we will fall through
            // and serialize full detailed type info.
            if (!detailedTypeInfo &&
                (!inMembersArray ||
                 (!std::is_same_v<TypeAliasType, T> && !std::is_same_v<ClassType, T> &&
                  !std::is_same_v<CovergroupType, T> && !std::is_same_v<EnumType, T>))) {
                writer.writeValue(printType());
                return;
            }

            // Even when printing detailed type info, if we're not in a members array prefer
            // to print links to typedefs and enums to reduce verbosity of output.
            if (!inMembersArray && includeAddrs &&
                (std::is_same_v<TypeAliasType, T> || std::is_same_v<EnumType, T>)) {
                writer.writeValue(printType());
                return;
            }

            // Avoid infinite loops with recursive types.
            if (!visiting.insert(&elem).second) {
                writer.writeValue(printType());
                return;
            }
        }

        // Skip uninstantiated blocks and instances.
        if constexpr (std::is_same_v<InstanceSymbol, T> ||
                      std::is_same_v<CheckerInstanceSymbol, T>) {
            if (elem.body.flags.has(InstanceFlags::Uninstantiated))
                return;
        }
        else if constexpr (std::is_same_v<GenerateBlockArraySymbol, T>) {
            if (!elem.valid)
                return;
        }
        else if constexpr (std::is_same_v<GenerateBlockSymbol, T>) {
            if (elem.isUninstantiated)
                return;
        }

        // Ignore built-in methods on class types.
        if constexpr (std::is_same_v<SubroutineSymbol, T>) {
            if (elem.flags.has(MethodFlags::BuiltIn | MethodFlags::Randomize))
                return;
        }

        if (elem.kind == SymbolKind::TransparentMember) {
            // Ignore transparent members, except in one particular case. The first time
            // we see a member of an enum type we should print it since all other references
            // to the enum will print links instead.
            if (auto ev = elem.template as<TransparentMemberSymbol>()
                              .wrapped.template as_if<EnumValueSymbol>();
                ev && includeAddrs && inMembersArray) {

                auto& enumType = ev->getType();
                if (printedEnums.insert(&enumType).second)
                    serialize(enumType, /* inMembersArray */ true);
            }
            return;
        }

        writer.startObject();
        write("name", elem.name);
        write("kind", toString(elem.kind));
        if (includeSourceInfo && elem.location && elem.location != SourceLocation::NoLocation) {
            if (auto sm = compilation.getSourceManager()) {
                write("source_file", sm->getFileName(elem.location));
                write("source_line", sm->getLineNumber(elem.location));
                write("source_column", sm->getColumnNumber(elem.location));
            }
        }

        if (includeAddrs)
            write("addr", uintptr_t(&elem));

        auto attributes = compilation.getAttributes(elem);
        if (!attributes.empty()) {
            startArray("attributes");
            for (auto attr : attributes)
                serialize(*attr);
            endArray();
        }

        if constexpr (std::is_base_of_v<ValueSymbol, T>) {
            if (elem.kind != SymbolKind::EnumValue)
                write("type", elem.getType());

            if (auto init = elem.getInitializer())
                write("initializer", *init);
        }

        if constexpr (std::is_base_of_v<Scope, T>) {
            if (!elem.empty()) {
                startArray("members");
                for (auto& member : elem.members())
                    serialize(member, /* inMembersArray */ true);
                endArray();
            }
        }

        if constexpr (!std::is_same_v<Symbol, T>) {
            elem.serializeTo(*this);
        }

        writer.endObject();

        if constexpr (std::is_base_of_v<Type, T>) {
            visiting.erase(&elem);
        }
    }
}

} // namespace slang::ast
