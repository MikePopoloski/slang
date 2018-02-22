//------------------------------------------------------------------------------
// TypePrinter.cpp
// Type printing utilities.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "TypePrinter.h"

namespace slang {

void TypePrinter::append(const Type& type) {
    type.visit(*this);
}

std::string TypePrinter::toString() const {
    return writer.str();
}

void TypePrinter::handle(const ScalarType& type) {
    switch (type.scalarKind) {
        case ScalarType::Bit: writer << "bit"; break;
        case ScalarType::Logic: writer << "logic"; break;
        case ScalarType::Reg: writer << "reg"; break;
        default: THROW_UNREACHABLE;
    }

    if (type.isSigned)
        writer << " signed";
}

void TypePrinter::handle(const PredefinedIntegerType& type) {
    switch (type.integerKind) {
        case PredefinedIntegerType::ShortInt: writer << "shortint"; break;
        case PredefinedIntegerType::Int: writer << "int"; break;
        case PredefinedIntegerType::LongInt: writer << "longint"; break;
        case PredefinedIntegerType::Byte: writer << "byte"; break;
        case PredefinedIntegerType::Integer: writer << "integer"; break;
        case PredefinedIntegerType::Time: writer << "time"; break;
        default: THROW_UNREACHABLE;
    }
    if (type.isSigned != PredefinedIntegerType::isDefaultSigned(type.integerKind))
        writer << (type.isSigned ? " signed" : " unsigned");
}

void TypePrinter::handle(const FloatingType& type) {
    switch (type.floatKind) {
        case FloatingType::Real: writer << "real"; break;
        case FloatingType::ShortReal: writer << "shortreal"; break;
        case FloatingType::RealTime: writer << "realtime"; break;
        default: THROW_UNREACHABLE;
    }
}

void TypePrinter::handle(const EnumType& type) {
    // TODO: base type?
    writer << "enum{";
    for (const auto& member : type.values()) {
        // TODO: write value with correct prefix
        writer.write("{}={},", member.name, member.value.integer().toString(LiteralBase::Decimal));
    }
    writer.pop_back();
    writer << "}";
}

void TypePrinter::handle(const PackedArrayType& type) {
    append(type.elementType);
    writer.write("[{}:{}]", type.range.left, type.range.right);
}

void TypePrinter::handle(const PackedStructType& type) {
    writer << "struct packed";
    if (type.isSigned)
        writer << " signed";
    
    appendStructMembers(type);
}

void TypePrinter::handle(const UnpackedStructType& type) {
    writer << "struct{";
    appendStructMembers(type);
}

void TypePrinter::handle(const VoidType&) {
    writer << "void";
}

void TypePrinter::handle(const NullType&) {
    writer << "null";
}

void TypePrinter::handle(const CHandleType&) {
    writer << "chandle";
}

void TypePrinter::handle(const StringType&) {
    writer << "string";
}

void TypePrinter::handle(const EventType&) {
    writer << "event";
}

void TypePrinter::handle(const TypeAliasType& type) {
    // Handle the target first.
    append(*type.targetType);

    // If our direct target is a user defined type, append its name here. Otherwise just ignore.
    switch (type.targetType->kind) {
        case SymbolKind::EnumType:
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
            // TODO: prepend scope name
            writer << type.name;
            break;
        default:
            break;
    }
}

void TypePrinter::handle(const ErrorType&) {
    writer << "<error>";
}

void TypePrinter::appendStructMembers(const Scope& scope) {
    writer << "{";
    for (const auto& member : scope.members()) {
        const auto& var = member.as<VariableSymbol>();
        append(*var.type);
        writer.write(" {};", var.name);
    }
    writer << "}";
}

}