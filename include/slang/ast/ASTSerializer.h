//------------------------------------------------------------------------------
//! @file ASTSerializer.h
//! @brief Support for serializing an AST
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Hash.h"
#include "slang/util/Util.h"

namespace slang {

class ConstantValue;
class JsonWriter;

} // namespace slang

namespace slang::ast {

class AssertionExpr;
class BinsSelectExpr;
class Compilation;
class Constraint;
class Expression;
class Pattern;
class Statement;
class Symbol;
class TimingControl;

/// A class that serializes AST nodes to JSON.
class SLANG_EXPORT ASTSerializer {
public:
    /// Constructs a new instance of the ASTSerializer class.
    ASTSerializer(Compilation& compilation, JsonWriter& writer);

    /// Sets a flag that indicates whether the addresses of AST objects
    /// should be included in the JSON output.
    void setIncludeAddresses(bool set) { includeAddrs = set; }

    /// Sets a flag that indicates whether source line and file
    /// information should be included in the JSON output.
    void setIncludeSourceInfo(bool set) { includeSourceInfo = set; }

    /// Sets a flag that indicates whether detailed type information
    /// is included in the output.
    void setDetailedTypeInfo(bool set) { detailedTypeInfo = set; }

    /// Serializes a symbol to JSON.
    void serialize(const Symbol& symbol, bool inMembersArray = false);

    /// Serializes an expression to JSON.
    void serialize(const Expression& expr);

    /// Serializes a statement to JSON.
    void serialize(const Statement& statement);

    /// Serializes a timing control to JSON.
    void serialize(const TimingControl& timing);

    /// Serializes a constraint to JSON.
    void serialize(const Constraint& constraint);

    /// Serializes an assertion expression to JSON.
    void serialize(const AssertionExpr& assertionExpr);

    /// Serializes a bin select expression to JSON.
    void serialize(const BinsSelectExpr& binsSelectExpr);

    /// Serializes a pattern to JSON.
    void serialize(const Pattern& pattern);

    /// Serializes the given verbatim string to JSON.
    void serialize(std::string_view value);

    /// Starts a new array in the serialized output.
    void startArray();

    /// Starts a new array property with the given name in the serialized output.
    void startArray(std::string_view name);

    /// Ends a previously started array.
    void endArray();

    /// Starts a new object in the serialized output.
    void startObject();

    /// Ends the previously started object.
    void endObject();

    /// Writes a property with the given name but no value (it is expected
    /// that you will write the value next).
    void writeProperty(std::string_view name);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, std::string_view value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, int64_t value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, uint64_t value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, double value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, bool value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const std::string& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const Symbol& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const ConstantValue& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const Expression& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const Statement& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const TimingControl& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const Constraint& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const AssertionExpr& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const BinsSelectExpr& value);

    /// Writes a property with the given value to the serialized output.
    void write(std::string_view name, const Pattern& value);

    /// Writes a property with a link to the given symbol to the serialized output.
    void writeLink(std::string_view name, const Symbol& value);

    /// Writes a property with the given signed integral value to the serialized output.
    template<std::signed_integral T>
    void write(std::string_view name, T value) {
        write(name, int64_t(value));
    }

    /// Writes a property with the given unsigned integral value to the serialized output.
    template<std::unsigned_integral T>
    void write(std::string_view name, T value) {
        write(name, uint64_t(value));
    }

    /// Writes a property with the given pointer value to the serialized output.
    template<typename T>
        requires std::is_pointer_v<T>
    void write(std::string_view name, T value) = delete;

    /// Writes a property with the given value to the serialized output.
    template<typename T>
    void write(std::string_view name, not_null<T> value) = delete;

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

    Compilation& compilation;
    JsonWriter& writer;
    bool includeAddrs = true;
    bool includeSourceInfo = false;
    bool detailedTypeInfo = false;
    flat_hash_set<const void*> visiting;
};

} // namespace slang::ast
