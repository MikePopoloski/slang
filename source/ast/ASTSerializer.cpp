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

void ASTSerializer::serialize(string_view value) {
    writer.writeValue(value);
}

void ASTSerializer::write(string_view name, string_view value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(string_view name, int64_t value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(string_view name, uint64_t value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(string_view name, double value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(string_view name, bool value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(string_view name, const std::string& value) {
    writer.writeProperty(name);
    writer.writeValue(value);
}

void ASTSerializer::write(string_view name, const Symbol& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(string_view name, const ConstantValue& value) {
    writer.writeProperty(name);
    writer.writeValue(value.toString());
}

void ASTSerializer::write(string_view name, const Expression& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(string_view name, const Statement& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(string_view name, const TimingControl& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(string_view name, const Constraint& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(string_view name, const AssertionExpr& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(string_view name, const BinsSelectExpr& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::write(string_view name, const Pattern& value) {
    writer.writeProperty(name);
    serialize(value);
}

void ASTSerializer::writeLink(string_view name, const Symbol& value) {
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

void ASTSerializer::startArray(string_view name) {
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

void ASTSerializer::writeProperty(string_view name) {
    writer.writeProperty(name);
}

template<typename T>
void ASTSerializer::visit(const T& elem, bool inMembersArray) {
    // TODO: remove once we no longer support gcc-10
    (void)inMembersArray;

    if constexpr (std::is_base_of_v<Expression, T>) {
        writer.startObject();
        write("kind", toString(elem.kind));
        write("type", *elem.type);

        if constexpr (!std::is_same_v<Expression, T>) {
            elem.serializeTo(*this);
        }

        EvalContext ctx(compilation, EvalFlags::CacheResults);
        ConstantValue constant = elem.eval(ctx);
        if (constant)
            write("constant", constant);

        writer.endObject();
    }
    else if constexpr (std::is_base_of_v<Statement, T>) {
        writer.startObject();
        write("kind", toString(elem.kind));

        if constexpr (!std::is_same_v<Statement, T>) {
            elem.serializeTo(*this);
        }

        writer.endObject();
    }
    else if constexpr (std::is_base_of_v<TimingControl, T> || std::is_base_of_v<Constraint, T> ||
                       std::is_base_of_v<AssertionExpr, T> ||
                       std::is_base_of_v<BinsSelectExpr, T> || std::is_base_of_v<Pattern, T>) {
        writer.startObject();
        write("kind", toString(elem.kind));
        if constexpr (!std::is_same_v<TimingControl, T> && !std::is_same_v<Constraint, T> &&
                      !std::is_same_v<AssertionExpr, T> && !std::is_same_v<BinsSelectExpr, T> &&
                      !std::is_same_v<Pattern, T>) {
            elem.serializeTo(*this);
        }
        writer.endObject();
    }
    else if constexpr (std::is_base_of_v<Type, T> && !std::is_same_v<TypeAliasType, T> &&
                       !std::is_same_v<ClassType, T> && !std::is_same_v<CovergroupType, T>) {
        writer.writeValue(elem.toString());
    }
    else {
        if constexpr (std::is_base_of_v<Type, T>) {
            if (!inMembersArray) {
                writer.writeValue(elem.toString());
                return;
            }
        }

        // Ignore built-in methods on class types.
        if constexpr (std::is_same_v<SubroutineSymbol, T>) {
            if (elem.flags.has(MethodFlags::NotConst | MethodFlags::Randomize))
                return;
        }

        writer.startObject();
        write("name", elem.name);
        write("kind", toString(elem.kind));

        if (includeAddrs)
            write("addr", uintptr_t(&elem));

        auto scope = elem.getParentScope();
        if (scope) {
            auto attributes = scope->getCompilation().getAttributes(elem);
            if (!attributes.empty()) {
                startArray("attributes");
                for (auto attr : attributes)
                    serialize(*attr);
                endArray();
            }
        }

        if constexpr (std::is_base_of_v<ValueSymbol, T>) {
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
    }
}

void ASTSerializer::visitInvalid(const Expression& expr) {
    visit(expr.as<InvalidExpression>());
}

void ASTSerializer::visitInvalid(const slang::ast::Statement& statement) {
    visit(statement.as<InvalidStatement>());
}

void ASTSerializer::visitInvalid(const slang::ast::TimingControl& timing) {
    visit(timing.as<InvalidTimingControl>());
}

void ASTSerializer::visitInvalid(const slang::ast::Constraint& constraint) {
    visit(constraint.as<InvalidConstraint>());
}

void ASTSerializer::visitInvalid(const slang::ast::AssertionExpr& expr) {
    visit(expr.as<InvalidAssertionExpr>());
}

void ASTSerializer::visitInvalid(const slang::ast::BinsSelectExpr& expr) {
    visit(expr.as<InvalidBinsSelectExpr>());
}

void ASTSerializer::visitInvalid(const slang::ast::Pattern& pattern) {
    visit(pattern.as<InvalidPattern>());
}

} // namespace slang::ast
