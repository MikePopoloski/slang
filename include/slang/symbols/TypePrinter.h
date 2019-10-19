//------------------------------------------------------------------------------
// TypePrinter.h
// Type printing utilities.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/AllTypes.h"
#include "slang/text/FormatBuffer.h"

namespace slang {

struct TypePrintingOptions {
    bool printAKA = false;
    bool addSingleQuotes = false;
    bool elideScopeNames = false;

    enum AnonymousTypeStyle { SystemName, FriendlyName } anonymousTypeStyle = SystemName;

    span<const Type* const> disambiguateTypes;
};

class TypePrinter {
public:
    void setOptions(const TypePrintingOptions& options_) { options = options_; }

    void append(const Type& type);

    std::string toString() const;

    void visit(const ScalarType& type, string_view overrideName);
    void visit(const PredefinedIntegerType& type, string_view overrideName);
    void visit(const FloatingType& type, string_view overrideName);
    void visit(const EnumType& type, string_view overrideName);
    void visit(const PackedArrayType& type, string_view overrideName);
    void visit(const PackedStructType& type, string_view overrideName);
    void visit(const PackedUnionType& type, string_view overrideName);
    void visit(const UnpackedArrayType& type, string_view overrideName);
    void visit(const UnpackedStructType& type, string_view overrideName);
    void visit(const UnpackedUnionType& type, string_view overrideName);
    void visit(const VoidType& type, string_view overrideName);
    void visit(const NullType& type, string_view overrideName);
    void visit(const CHandleType& type, string_view overrideName);
    void visit(const StringType& type, string_view overrideName);
    void visit(const EventType& type, string_view overrideName);
    void visit(const TypeAliasType& type, string_view overrideName);
    void visit(const ErrorType& type, string_view overrideName);

    template<typename T>
    void visit(const T&, string_view) {}

private:
    void appendMembers(const Scope& scope);
    void printScope(const Scope* scope);

    FormatBuffer buffer;
    TypePrintingOptions options;
};

} // namespace slang