//------------------------------------------------------------------------------
// TypePrinter.cpp
// Type printing utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/TypePrinter.h"

#include "../text/FormatBuffer.h"

#include "slang/symbols/ASTVisitor.h"

namespace slang {

static std::string getLexicalPath(const Scope* scope) {
    if (!scope || scope->asSymbol().kind == SymbolKind::CompilationUnit)
        return "";

    std::string str;
    auto& sym = scope->asSymbol();
    sym.getLexicalPath(str);

    if (sym.kind == SymbolKind::Package || sym.kind == SymbolKind::ClassType)
        str.append("::");
    else
        str.push_back('.');

    return str;
}

TypePrinter::TypePrinter() : buffer(std::make_unique<FormatBuffer>()) {
}

TypePrinter::~TypePrinter() = default;

void TypePrinter::append(const Type& type) {
    if (options.addSingleQuotes)
        buffer->append("'");
    type.visit(*this, "");
    if (options.addSingleQuotes)
        buffer->append("'");
}

std::string TypePrinter::toString() const {
    return buffer->str();
}

void TypePrinter::visit(const ScalarType& type, string_view) {
    // clang-format off
    switch (type.scalarKind) {
        case ScalarType::Bit: buffer->append("bit"); break;
        case ScalarType::Logic: buffer->append("logic"); break;
        case ScalarType::Reg: buffer->append("reg"); break;
        default: THROW_UNREACHABLE;
    }
    // clang-format on

    if (type.isSigned)
        buffer->append(" signed");
}

void TypePrinter::visit(const PredefinedIntegerType& type, string_view) {
    // clang-format off
    switch (type.integerKind) {
        case PredefinedIntegerType::ShortInt: buffer->append("shortint"); break;
        case PredefinedIntegerType::Int: buffer->append("int"); break;
        case PredefinedIntegerType::LongInt: buffer->append("longint"); break;
        case PredefinedIntegerType::Byte: buffer->append("byte"); break;
        case PredefinedIntegerType::Integer: buffer->append("integer"); break;
        case PredefinedIntegerType::Time: buffer->append("time"); break;
        default: THROW_UNREACHABLE;
    }
    // clang-format on

    if (type.isSigned != PredefinedIntegerType::isDefaultSigned(type.integerKind))
        buffer->append(type.isSigned ? " signed" : " unsigned");
}

void TypePrinter::visit(const FloatingType& type, string_view) {
    // clang-format off
    switch (type.floatKind) {
        case FloatingType::Real: buffer->append("real"); break;
        case FloatingType::ShortReal: buffer->append("shortreal"); break;
        case FloatingType::RealTime: buffer->append("realtime"); break;
        default: THROW_UNREACHABLE;
    }
    // clang-format on
}

void TypePrinter::visit(const EnumType& type, string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        printScope(type.getParentScope());

        if (overrideName.empty())
            buffer->append("<unnamed enum>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("enum{");

        bool first = true;
        for (const auto& member : type.values()) {
            if (!first)
                buffer->append(",");

            // TODO: write value with correct prefix
            buffer->format("{}={}", member.name,
                           member.getValue().integer().toString(LiteralBase::Decimal));
            first = false;
        }
        buffer->append("}");

        if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("e${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const PackedArrayType& type, string_view) {
    SmallVectorSized<ConstantRange, 8> dims;
    const PackedArrayType* curr = &type;
    while (true) {
        dims.append(curr->range);
        if (!curr->elementType.isPackedArray())
            break;

        curr = &curr->elementType.getCanonicalType().as<PackedArrayType>();
    }

    curr->elementType.visit(*this, "");
    for (auto& range : dims)
        buffer->format("[{}:{}]", range.left, range.right);
}

void TypePrinter::visit(const PackedStructType& type, string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        // printScope(type.getParentScope());

        if (overrideName.empty())
            buffer->append("<unnamed packed struct>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("struct packed");
        if (type.isSigned)
            buffer->append(" signed");

        appendMembers(type);

        if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("s${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const PackedUnionType& type, string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        // printScope(type.getParentScope());

        if (overrideName.empty())
            buffer->append("<unnamed packed union>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("union packed");
        if (type.isSigned)
            buffer->append(" signed");

        appendMembers(type);

        if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("u${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const UnpackedArrayType& type, string_view) {
    SmallVectorSized<ConstantRange, 8> dims;
    const UnpackedArrayType* curr = &type;
    while (true) {
        dims.append(curr->range);
        if (!curr->elementType.isUnpackedArray())
            break;

        curr = &curr->elementType.getCanonicalType().as<UnpackedArrayType>();
    }

    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        buffer->append("unpacked array ");
        for (auto& range : dims) {
            if (!range.isLittleEndian() && range.lower() == 0)
                buffer->format("[{}]", range.width());
            else
                buffer->format("[{}:{}]", range.left, range.right);
        }

        buffer->append(" of ");
        append(curr->elementType);
    }
    else {
        append(curr->elementType);
        buffer->append("$");

        for (auto& range : dims)
            buffer->format("[{}:{}]", range.left, range.right);
    }
}

void TypePrinter::visit(const UnpackedStructType& type, string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        // printScope(type.getParentScope());
        if (overrideName.empty())
            buffer->append("<unnamed unpacked struct>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("struct");
        appendMembers(type);

        if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("s${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const UnpackedUnionType& type, string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        // printScope(type.getParentScope());
        if (overrideName.empty())
            buffer->append("<unnamed unpacked union>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("union");
        appendMembers(type);

        if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("u${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const VoidType&, string_view) {
    buffer->append("void");
}

void TypePrinter::visit(const NullType&, string_view) {
    buffer->append("null");
}

void TypePrinter::visit(const CHandleType&, string_view) {
    buffer->append("chandle");
}

void TypePrinter::visit(const StringType&, string_view) {
    buffer->append("string");
}

void TypePrinter::visit(const EventType&, string_view) {
    buffer->append("event");
}

void TypePrinter::visit(const TypeAliasType& type, string_view overrideName) {
    if (!overrideName.empty()) {
        type.targetType.getType().visit(*this, overrideName);
    }
    else if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        type.targetType.getType().visit(*this, type.name);
    }
    else {
        std::string path = getLexicalPath(type.getParentScope());
        path.append(type.name);
        type.targetType.getType().visit(*this, path);
    }
}

void TypePrinter::visit(const ErrorType&, string_view) {
    buffer->append("<error>");
}

void TypePrinter::appendMembers(const Scope& scope) {
    buffer->append("{");
    for (auto& member : scope.members()) {
        auto& var = member.as<VariableSymbol>();
        append(var.getType());
        buffer->format(" {};", var.name);
    }
    buffer->append("}");
}

void TypePrinter::printScope(const Scope* scope) {
    buffer->append(getLexicalPath(scope));
}

} // namespace slang