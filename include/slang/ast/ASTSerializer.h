//------------------------------------------------------------------------------
//! @file ASTSerializer.h
//! @brief Support for serializing an AST
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/text/Json.h"
#include "slang/util/Util.h"

namespace slang {

class ConstantValue;

} // namespace slang

namespace slang::ast {

class AssertionExpr;
class AttributeSymbol;
class BinsSelectExpr;
class Compilation;
class Constraint;
class Expression;
class Pattern;
class Statement;
class Symbol;
class Type;
class TimingControl;

class SLANG_EXPORT ASTSerializer {
public:
    ASTSerializer(Compilation& compilation, JsonWriter& writer);

    void setIncludeAddresses(bool set) { includeAddrs = set; }

    void serialize(const Symbol& symbol, bool inMembersArray = false);
    void serialize(const Expression& expr);
    void serialize(const Statement& statement);
    void serialize(const TimingControl& timing);
    void serialize(const Constraint& constraint);
    void serialize(const AssertionExpr& assertionExpr);
    void serialize(const BinsSelectExpr& binsSelectExpr);
    void serialize(const Pattern& pattern);
    void serialize(std::string_view value);

    void startArray();
    void startArray(string_view name);
    void endArray();
    void startObject();
    void endObject();
    void writeProperty(string_view name);

    void write(string_view name, string_view value);
    void write(string_view name, int64_t value);
    void write(string_view name, uint64_t value);
    void write(string_view name, double value);
    void write(string_view name, bool value);
    void write(string_view name, const std::string& value);
    void write(string_view name, const Symbol& value);
    void write(string_view name, const ConstantValue& value);
    void write(string_view name, const Expression& value);
    void write(string_view name, const Statement& value);
    void write(string_view name, const TimingControl& value);
    void write(string_view name, const Constraint& value);
    void write(string_view name, const AssertionExpr& value);
    void write(string_view name, const BinsSelectExpr& value);
    void write(string_view name, const Pattern& value);

    void writeLink(string_view name, const Symbol& value);

    template<typename T, std::enable_if_t<std::is_integral_v<T> && std::is_signed_v<T>, int> = 0>
    void write(string_view name, T value) {
        write(name, int64_t(value));
    }

    template<typename T, std::enable_if_t<std::is_integral_v<T> && std::is_unsigned_v<T>, int> = 0>
    void write(string_view name, T value) {
        write(name, uint64_t(value));
    }

    template<typename T, std::enable_if_t<std::is_pointer_v<T>, int> = 0>
    void write(string_view name, T value) = delete;

    template<typename T>
    void write(string_view name, not_null<T> value) = delete;

private:
    friend Symbol;
    friend Expression;
    friend Statement;
    friend TimingControl;
    friend Constraint;
    friend AssertionExpr;
    friend BinsSelectExpr;
    friend Pattern;

    template<typename T>
    void visit(const T& symbol, bool inMembersArray = false);

    void visitInvalid(const Expression& expr);
    void visitInvalid(const Statement& statement);
    void visitInvalid(const TimingControl& timing);
    void visitInvalid(const Constraint& timing);
    void visitInvalid(const AssertionExpr& expr);
    void visitInvalid(const BinsSelectExpr& expr);
    void visitInvalid(const Pattern& pattern);

    Compilation& compilation;
    JsonWriter& writer;
    bool includeAddrs = true;
};

} // namespace slang::ast
