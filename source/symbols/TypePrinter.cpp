//------------------------------------------------------------------------------
// TypePrinter.cpp
// Type printing utilities.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/TypePrinter.h"

namespace slang {

void TypePrinter::append(const Type& type) {
    type.visit(*this);
}

std::string TypePrinter::toString() const {
    return to_string(buffer);
}

void TypePrinter::handle(const ScalarType& type) {
    switch (type.scalarKind) {
        case ScalarType::Bit: buffer << "bit"; break;
        case ScalarType::Logic: buffer << "logic"; break;
        case ScalarType::Reg: buffer << "reg"; break;
        default: THROW_UNREACHABLE;
    }

    if (type.isSigned)
        buffer << " signed";
}

void TypePrinter::handle(const PredefinedIntegerType& type) {
    switch (type.integerKind) {
        case PredefinedIntegerType::ShortInt: buffer << "shortint"; break;
        case PredefinedIntegerType::Int: buffer << "int"; break;
        case PredefinedIntegerType::LongInt: buffer << "longint"; break;
        case PredefinedIntegerType::Byte: buffer << "byte"; break;
        case PredefinedIntegerType::Integer: buffer << "integer"; break;
        case PredefinedIntegerType::Time: buffer << "time"; break;
        default: THROW_UNREACHABLE;
    }
    if (type.isSigned != PredefinedIntegerType::isDefaultSigned(type.integerKind))
        buffer << (type.isSigned ? " signed" : " unsigned");
}

void TypePrinter::handle(const FloatingType& type) {
    switch (type.floatKind) {
        case FloatingType::Real: buffer << "real"; break;
        case FloatingType::ShortReal: buffer << "shortreal"; break;
        case FloatingType::RealTime: buffer << "realtime"; break;
        default: THROW_UNREACHABLE;
    }
}

void TypePrinter::handle(const EnumType& type) {
    // TODO: base type?
    buffer << "enum{";
    for (const auto& member : type.values()) {
        // TODO: write value with correct prefix
        format_to(buffer, "{}={},", member.name, member.value.integer().toString(LiteralBase::Decimal));
    }
    buffer.pop_back();
    buffer << "}";
}

void TypePrinter::handle(const PackedArrayType& type) {
    append(type.elementType);
    format_to(buffer, "[{}:{}]", type.range.left, type.range.right);
}

void TypePrinter::handle(const PackedStructType& type) {
    buffer << "struct packed";
    if (type.isSigned)
        buffer << " signed";

    appendStructMembers(type);
}

void TypePrinter::handle(const UnpackedStructType& type) {
    buffer << "struct{";
    appendStructMembers(type);
}

void TypePrinter::handle(const VoidType&) {
    buffer << "void";
}

void TypePrinter::handle(const NullType&) {
    buffer << "null";
}

void TypePrinter::handle(const CHandleType&) {
    buffer << "chandle";
}

void TypePrinter::handle(const StringType&) {
    buffer << "string";
}

void TypePrinter::handle(const EventType&) {
    buffer << "event";
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
            buffer << type.name;
            break;
        default:
            break;
    }
}

void TypePrinter::handle(const ErrorType&) {
    buffer << "<error>";
}

void TypePrinter::handle(const NetType& type) {
    switch (type.netKind) {
        case NetType::Unknown: buffer << "<error-nettype>"; break;
        case NetType::Wire: buffer << "wire"; break;
        case NetType::WAnd:  buffer << "wand"; break;
        case NetType::WOr: buffer << "wor"; break;
        case NetType::Tri: buffer << "tri"; break;
        case NetType::TriAnd: buffer << "triand"; break;
        case NetType::TriOr: buffer << "trior"; break;
        case NetType::Tri0: buffer << "tri0"; break;
        case NetType::Tri1: buffer << "tri1"; break;
        case NetType::TriReg: buffer << "trireg"; break;
        case NetType::Supply0: buffer << "supply0"; break;
        case NetType::Supply1: buffer << "supply1"; break;
        case NetType::UWire: buffer << "uwire"; break;
        case NetType::UserDefined: break; // TODO:
        case NetType::Alias: break; // TODO:
    }
}

void TypePrinter::appendStructMembers(const Scope& scope) {
    buffer << "{";
    for (const auto& member : scope.members()) {
        const auto& var = member.as<VariableSymbol>();
        append(*var.type);
        format_to(buffer, " {};", var.name);
    }
    buffer << "}";
}

}