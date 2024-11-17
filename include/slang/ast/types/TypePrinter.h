//------------------------------------------------------------------------------
//! @file TypePrinter.h
//! @brief Type printing utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/DiagArgFormatter.h"

namespace slang {
class FormatBuffer;
}

namespace slang::ast {

class ClassType;
class CovergroupType;

/// A collection of type printing options.
struct SLANG_EXPORT TypePrintingOptions {
    /// Add single quotes around type names.
    bool addSingleQuotes = false;

    /// Elide the names of scopes containing the types.
    bool elideScopeNames = false;

    /// Print an 'aka' note when unwrapping typedefs.
    bool printAKA = false;

    /// Skip over scoped type names completely.
    bool skipScopedTypeNames = false;

    /// Skip expanding typedefs.
    bool skipTypeDefs = false;

    /// Include the enum's base type.
    bool fullEnumType = false;

    /// Selects a style for anonymous types, either the system ID name
    /// or a more human-friendly name.
    enum AnonymousTypeStyle { SystemName, FriendlyName } anonymousTypeStyle = SystemName;
};

/// A utility class that prints a SystemVerilog type to a string.
class SLANG_EXPORT TypePrinter {
public:
    /// Options that control type printing.
    TypePrintingOptions options;

    /// Constructs a new type printer.
    TypePrinter();
    ~TypePrinter();

    /// Append the given type to the printer's string buffer.
    void append(const Type& type);

    /// Clear the printer's string buffer.
    void clear();

    /// @returns the printer's string buffer as a copy.
    std::string toString() const;

    void visit(const ScalarType& type, std::string_view overrideName);
    void visit(const PredefinedIntegerType& type, std::string_view overrideName);
    void visit(const FloatingType& type, std::string_view overrideName);
    void visit(const EnumType& type, std::string_view overrideName);
    void visit(const PackedArrayType& type, std::string_view overrideName);
    void visit(const PackedStructType& type, std::string_view overrideName);
    void visit(const PackedUnionType& type, std::string_view overrideName);
    void visit(const FixedSizeUnpackedArrayType& type, std::string_view overrideName);
    void visit(const DynamicArrayType& type, std::string_view overrideName);
    void visit(const DPIOpenArrayType& type, std::string_view overrideName);
    void visit(const AssociativeArrayType& type, std::string_view overrideName);
    void visit(const QueueType& type, std::string_view overrideName);
    void visit(const UnpackedStructType& type, std::string_view overrideName);
    void visit(const UnpackedUnionType& type, std::string_view overrideName);
    void visit(const VoidType& type, std::string_view overrideName);
    void visit(const NullType& type, std::string_view overrideName);
    void visit(const CHandleType& type, std::string_view overrideName);
    void visit(const StringType& type, std::string_view overrideName);
    void visit(const EventType& type, std::string_view overrideName);
    void visit(const UnboundedType& type, std::string_view overrideName);
    void visit(const TypeRefType& type, std::string_view overrideName);
    void visit(const UntypedType& type, std::string_view overrideName);
    void visit(const SequenceType& type, std::string_view overrideName);
    void visit(const PropertyType& type, std::string_view overrideName);
    void visit(const VirtualInterfaceType& type, std::string_view overrideName);
    void visit(const ClassType& type, std::string_view overrideName);
    void visit(const CovergroupType& type, std::string_view overrideName);
    void visit(const TypeAliasType& type, std::string_view overrideName);
    void visit(const ErrorType& type, std::string_view overrideName);

    template<typename T>
    void visit(const T&, std::string_view) {}

private:
    void appendMembers(const Scope& scope);
    void printUnpackedArray(const Type& type);
    void printUnpackedArrayDim(const Type& type);
    void printScope(const Scope* scope);
    void printAKA(const Type& type);

    std::unique_ptr<FormatBuffer> buffer;
};

/// A diagnostic argument formatter specifically for formatting types.
class SLANG_EXPORT TypeArgFormatter : public DiagArgFormatter {
public:
    /// Constructs a new type arg formatter.
    TypeArgFormatter();

    /// Set the options to use when formatting types.
    void setOptions(const TypePrintingOptions& options) { printer.options = options; }

    void startMessage(const Diagnostic& diag) final;
    std::string format(const std::any& arg) final;

private:
    TypePrinter printer;
    flat_hash_set<const Type*> seenTypes;
    flat_hash_set<const Type*> typesToDisambiguate;
};

} // namespace slang::ast
