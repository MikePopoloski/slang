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

struct SLANG_EXPORT TypePrintingOptions {
    bool addSingleQuotes = false;
    bool elideScopeNames = false;
    bool printAKA = false;
    bool skipScopedTypeNames = false;
    bool fullEnumType = false;

    enum AnonymousTypeStyle { SystemName, FriendlyName } anonymousTypeStyle = SystemName;
};

class SLANG_EXPORT TypePrinter {
public:
    TypePrintingOptions options;

    TypePrinter();
    ~TypePrinter();

    void append(const Type& type);
    void clear();

    std::string toString() const;

    void visit(const ScalarType& type, string_view overrideName);
    void visit(const PredefinedIntegerType& type, string_view overrideName);
    void visit(const FloatingType& type, string_view overrideName);
    void visit(const EnumType& type, string_view overrideName);
    void visit(const PackedArrayType& type, string_view overrideName);
    void visit(const PackedStructType& type, string_view overrideName);
    void visit(const PackedUnionType& type, string_view overrideName);
    void visit(const FixedSizeUnpackedArrayType& type, string_view overrideName);
    void visit(const DynamicArrayType& type, string_view overrideName);
    void visit(const AssociativeArrayType& type, string_view overrideName);
    void visit(const QueueType& type, string_view overrideName);
    void visit(const UnpackedStructType& type, string_view overrideName);
    void visit(const UnpackedUnionType& type, string_view overrideName);
    void visit(const VoidType& type, string_view overrideName);
    void visit(const NullType& type, string_view overrideName);
    void visit(const CHandleType& type, string_view overrideName);
    void visit(const StringType& type, string_view overrideName);
    void visit(const EventType& type, string_view overrideName);
    void visit(const UnboundedType& type, string_view overrideName);
    void visit(const TypeRefType& type, string_view overrideName);
    void visit(const UntypedType& type, string_view overrideName);
    void visit(const SequenceType& type, string_view overrideName);
    void visit(const PropertyType& type, string_view overrideName);
    void visit(const VirtualInterfaceType& type, string_view overrideName);
    void visit(const ClassType& type, string_view overrideName);
    void visit(const CovergroupType& type, string_view overrideName);
    void visit(const TypeAliasType& type, string_view overrideName);
    void visit(const ErrorType& type, string_view overrideName);

    template<typename T>
    void visit(const T&, string_view) {}

private:
    void appendMembers(const Scope& scope);
    void printUnpackedArray(const Type& type);
    void printUnpackedArrayDim(const Type& type);
    void printScope(const Scope* scope);
    void printAKA(const Type& type);

    std::unique_ptr<FormatBuffer> buffer;
};

class SLANG_EXPORT TypeArgFormatter : public DiagArgFormatter {
public:
    TypeArgFormatter();

    void setOptions(const TypePrintingOptions& options) { printer.options = options; }

    void startMessage(const Diagnostic& diag) final;
    std::string format(const std::any& arg) final;

private:
    TypePrinter printer;
    flat_hash_set<const Type*> seenTypes;
};

} // namespace slang::ast
