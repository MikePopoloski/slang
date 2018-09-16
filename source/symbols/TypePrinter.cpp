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
    return buffer.str();
}

void TypePrinter::handle(const ScalarType& type) {
    switch (type.scalarKind) {
        case ScalarType::Bit: buffer.append("bit"); break;
        case ScalarType::Logic: buffer.append("logic"); break;
        case ScalarType::Reg: buffer.append("reg"); break;
        default: THROW_UNREACHABLE;
    }

    if (type.isSigned)
        buffer.append(" signed");
}

void TypePrinter::handle(const PredefinedIntegerType& type) {
    switch (type.integerKind) {
        case PredefinedIntegerType::ShortInt: buffer.append("shortint"); break;
        case PredefinedIntegerType::Int: buffer.append("int"); break;
        case PredefinedIntegerType::LongInt: buffer.append("longint"); break;
        case PredefinedIntegerType::Byte: buffer.append("byte"); break;
        case PredefinedIntegerType::Integer: buffer.append("integer"); break;
        case PredefinedIntegerType::Time: buffer.append("time"); break;
        default: THROW_UNREACHABLE;
    }
    if (type.isSigned != PredefinedIntegerType::isDefaultSigned(type.integerKind))
        buffer.append((type.isSigned ? " signed" : " unsigned"));
}

void TypePrinter::handle(const FloatingType& type) {
    switch (type.floatKind) {
        case FloatingType::Real: buffer.append("real"); break;
        case FloatingType::ShortReal: buffer.append("shortreal"); break;
        case FloatingType::RealTime: buffer.append("realtime"); break;
        default: THROW_UNREACHABLE;
    }
}

void TypePrinter::handle(const EnumType& type) {
    // TODO: base type?
    buffer.append("enum{");
    for (const auto& member : type.values()) {
        // TODO: write value with correct prefix
        buffer.format("{}={},", member.name, member.getValue().integer().toString(LiteralBase::Decimal));
    }
    buffer.pop_back();
    buffer.append("}");
}

void TypePrinter::handle(const PackedArrayType& type) {
    append(type.elementType);
    buffer.format("[{}:{}]", type.range.left, type.range.right);
}

void TypePrinter::handle(const PackedStructType& type) {
    buffer.append("struct packed");
    if (type.isSigned)
        buffer.append(" signed");

    appendStructMembers(type);
}

void TypePrinter::handle(const UnpackedArrayType& type) {
    SmallVectorSized<ConstantRange, 8> dims;
    const UnpackedArrayType* curr = &type;
    while (true) {
        dims.append(curr->range);
        if (!curr->elementType.isUnpackedArray())
            break;

        curr = &curr->elementType.getCanonicalType().as<UnpackedArrayType>();
    }

    append(curr->elementType);
    buffer.append("$");

    for (auto& range : dims)
        buffer.format("[{}:{}]", range.left, range.right);
}

void TypePrinter::handle(const UnpackedStructType& type) {
    buffer.append("struct");
    appendStructMembers(type);
}

void TypePrinter::handle(const VoidType&) {
    buffer.append("void");
}

void TypePrinter::handle(const NullType&) {
    buffer.append("null");
}

void TypePrinter::handle(const CHandleType&) {
    buffer.append("chandle");
}

void TypePrinter::handle(const StringType&) {
    buffer.append("string");
}

void TypePrinter::handle(const EventType&) {
    buffer.append("event");
}

void TypePrinter::handle(const TypeAliasType& type) {
    // Handle the target first.
    append(type.targetType.getType());

    // If our direct target is a user defined type, append its name here. Otherwise just ignore.
    switch (type.targetType.getType().kind) {
        case SymbolKind::EnumType:
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
            // TODO: prepend scope name
            buffer.append(type.name);
            break;
        default:
            break;
    }
}

void TypePrinter::handle(const ErrorType&) {
    buffer.append("<error>");
}

void TypePrinter::handle(const NetType& type) {
    switch (type.netKind) {
        case NetType::Unknown: buffer.append("<error-nettype>"); break;
        case NetType::Wire: buffer.append("wire"); break;
        case NetType::WAnd:  buffer.append("wand"); break;
        case NetType::WOr: buffer.append("wor"); break;
        case NetType::Tri: buffer.append("tri"); break;
        case NetType::TriAnd: buffer.append("triand"); break;
        case NetType::TriOr: buffer.append("trior"); break;
        case NetType::Tri0: buffer.append("tri0"); break;
        case NetType::Tri1: buffer.append("tri1"); break;
        case NetType::TriReg: buffer.append("trireg"); break;
        case NetType::Supply0: buffer.append("supply0"); break;
        case NetType::Supply1: buffer.append("supply1"); break;
        case NetType::UWire: buffer.append("uwire"); break;
        case NetType::UserDefined: break; // TODO:
        case NetType::Alias: break; // TODO:
    }
}

void TypePrinter::appendStructMembers(const Scope& scope) {
    buffer.append("{");
    for (auto& member : scope.members()) {
        auto& var = member.as<VariableSymbol>();
        append(var.getType());
        buffer.format(" {};", var.name);
    }
    buffer.append("}");
}

}