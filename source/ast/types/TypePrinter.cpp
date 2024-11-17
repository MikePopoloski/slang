//------------------------------------------------------------------------------
// TypePrinter.cpp
// Type printing utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/types/TypePrinter.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/text/FormatBuffer.h"

namespace slang::ast {

static std::string getLexicalPath(const Scope* scope) {
    if (!scope || scope->asSymbol().kind == SymbolKind::CompilationUnit)
        return "";

    std::string str;
    auto& sym = scope->asSymbol();
    sym.getLexicalPath(str);

    if (sym.kind == SymbolKind::Package || sym.kind == SymbolKind::ClassType ||
        sym.kind == SymbolKind::CovergroupType) {
        str.append("::");
    }
    else {
        str.push_back('.');
    }

    return str;
}

TypePrinter::TypePrinter() : buffer(std::make_unique<FormatBuffer>()) {
}

TypePrinter::~TypePrinter() = default;

void TypePrinter::append(const Type& type) {
    if (options.addSingleQuotes)
        buffer->append("'");

    if (options.printAKA && type.kind == SymbolKind::TypeAlias) {
        if (!options.elideScopeNames)
            buffer->append(getLexicalPath(type.getParentScope()));
        buffer->append(type.name);
    }
    else {
        type.visit(*this, ""sv);
    }

    if (options.addSingleQuotes)
        buffer->append("'");

    if (options.printAKA && type.kind == SymbolKind::TypeAlias)
        printAKA(type);
}

void TypePrinter::clear() {
    buffer->clear();
}

std::string TypePrinter::toString() const {
    return buffer->str();
}

void TypePrinter::visit(const ScalarType& type, std::string_view) {
    buffer->append(type.name);
    if (type.isSigned)
        buffer->append(" signed");
}

void TypePrinter::visit(const PredefinedIntegerType& type, std::string_view) {
    buffer->append(type.name);
    if (type.isSigned != PredefinedIntegerType::isDefaultSigned(type.integerKind))
        buffer->append(type.isSigned ? " signed" : " unsigned");
}

void TypePrinter::visit(const FloatingType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const EnumType& type, std::string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        printScope(type.getParentScope());

        if (!type.name.empty())
            buffer->append(type.name);
        else if (overrideName.empty())
            buffer->append("<unnamed enum>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("enum");
        if (options.fullEnumType) {
            buffer->append(" ");
            buffer->append(type.baseType.toString());
        }
        buffer->append("{");

        bool first = true;
        for (const auto& member : type.values()) {
            if (!first)
                buffer->append(",");

            auto& value = member.getValue().integer();
            buffer->format("{}={}", member.name,
                           value.toString(LiteralBase::Decimal, /* includeBase */ true));
            first = false;
        }
        buffer->append("}");

        if (options.skipScopedTypeNames) {
            // Nothing to do here.
        }
        else if (!overrideName.empty()) {
            buffer->append(overrideName);
        }
        else {
            printScope(type.getParentScope());
            if (type.name.empty())
                buffer->format("e${}", type.systemId);
            else
                buffer->append(type.name);
        }
    }
}

void TypePrinter::visit(const PackedArrayType& type, std::string_view) {
    SmallVector<ConstantRange, 8> dims;
    const PackedArrayType* curr = &type;
    while (true) {
        dims.push_back(curr->range);
        if (!curr->elementType.isPackedArray())
            break;

        curr = &curr->elementType.getCanonicalType().as<PackedArrayType>();
    }

    curr->elementType.visit(*this, ""sv);
    for (auto& range : dims)
        buffer->format("[{}:{}]", range.left, range.right);
}

void TypePrinter::visit(const PackedStructType& type, std::string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        printScope(type.getParentScope());

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

        if (options.skipScopedTypeNames)
            ;
        else if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("s${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const PackedUnionType& type, std::string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        printScope(type.getParentScope());

        if (overrideName.empty())
            buffer->append("<unnamed packed union>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("union packed");
        if (type.isSigned)
            buffer->append(" signed");

        if (type.isTagged)
            buffer->append(" tagged");

        appendMembers(type);

        if (options.skipScopedTypeNames)
            ;
        else if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("u${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const FixedSizeUnpackedArrayType& type, std::string_view) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        buffer->append("unpacked array ");
        if (!type.range.isLittleEndian() && type.range.lower() == 0)
            buffer->format("[{}]", type.range.width());
        else
            buffer->format("[{}:{}]", type.range.left, type.range.right);

        buffer->append(" of ");
        type.elementType.visit(*this, ""sv);
    }
    else {
        printUnpackedArray(type);
    }
}

void TypePrinter::visit(const DynamicArrayType& type, std::string_view) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        buffer->append("dynamic array of ");
        type.elementType.visit(*this, ""sv);
    }
    else {
        printUnpackedArray(type);
    }
}

void TypePrinter::visit(const DPIOpenArrayType& type, std::string_view) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        if (type.isPacked) {
            type.elementType.visit(*this, ""sv);
            buffer->append("[]");
        }
        else {
            buffer->append("unpacked array [] of ");
            type.elementType.visit(*this, ""sv);
        }
    }
    else {
        printUnpackedArray(type);
    }
}

void TypePrinter::visit(const AssociativeArrayType& type, std::string_view) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        buffer->append("associative array [");
        if (type.indexType)
            type.indexType->visit(*this, ""sv);
        else
            buffer->append("*");

        buffer->append("] of ");
        type.elementType.visit(*this, ""sv);
    }
    else {
        printUnpackedArray(type);
    }
}

void TypePrinter::visit(const QueueType& type, std::string_view) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        buffer->append("queue of ");
        type.elementType.visit(*this, ""sv);
    }
    else {
        printUnpackedArray(type);
    }
}

void TypePrinter::visit(const UnpackedStructType& type, std::string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        printScope(type.getParentScope());

        if (overrideName.empty())
            buffer->append("<unnamed unpacked struct>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("struct");
        appendMembers(type);

        if (options.skipScopedTypeNames)
            ;
        else if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("s${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const UnpackedUnionType& type, std::string_view overrideName) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        printScope(type.getParentScope());

        if (overrideName.empty())
            buffer->append("<unnamed unpacked union>");
        else
            buffer->append(overrideName);
    }
    else {
        buffer->append("union");
        if (type.isTagged)
            buffer->append(" tagged");

        appendMembers(type);

        if (options.skipScopedTypeNames)
            ;
        else if (!overrideName.empty())
            buffer->append(overrideName);
        else {
            printScope(type.getParentScope());
            buffer->format("u${}", type.systemId);
        }
    }
}

void TypePrinter::visit(const VoidType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const NullType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const CHandleType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const StringType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const EventType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const UnboundedType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const TypeRefType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const UntypedType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const SequenceType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const PropertyType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const ClassType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const CovergroupType& type, std::string_view) {
    buffer->append(type.name);
}

void TypePrinter::visit(const VirtualInterfaceType& type, std::string_view) {
    if (options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        if (!type.isRealIface)
            buffer->append("virtual ");
        buffer->append("interface ");
    }

    buffer->append(type.iface.getDefinition().name);

    auto params = type.iface.body.getParameters();
    if (!params.empty()) {
        buffer->append("#(");
        for (auto param : params) {
            buffer->format("{}=", param->symbol.name);
            if (param->symbol.kind == SymbolKind::TypeParameter)
                append(param->symbol.as<TypeParameterSymbol>().targetType.getType());
            else
                buffer->append(param->symbol.as<ParameterSymbol>().getValue().toString());
            buffer->append(",");
        }

        buffer->pop_back();
        buffer->append(")");
    }

    if (type.modport)
        buffer->format(".{}", type.modport->name);
}

void TypePrinter::visit(const TypeAliasType& type, std::string_view overrideName) {
    std::string downstreamOverrideName;
    if (!overrideName.empty()) {
        downstreamOverrideName = overrideName;
    }
    else if (options.elideScopeNames ||
             options.anonymousTypeStyle == TypePrintingOptions::FriendlyName) {
        downstreamOverrideName = type.name;
    }
    else {
        std::string path = getLexicalPath(type.getParentScope());
        path.append(type.name);
        downstreamOverrideName = path;
    }

    if (options.skipTypeDefs) {
        buffer->append(downstreamOverrideName);
    }
    else {
        type.targetType.getType().visit(*this, downstreamOverrideName);
    }
}

void TypePrinter::visit(const ErrorType&, std::string_view) {
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

void TypePrinter::printUnpackedArray(const Type& type) {
    const Type* elemType = &type;
    do {
        elemType = elemType->getArrayElementType();
    } while (elemType->isUnpackedArray());

    elemType->visit(*this, ""sv);
    buffer->append("$");
    printUnpackedArrayDim(type.getCanonicalType());
}

void TypePrinter::printUnpackedArrayDim(const Type& type) {
    switch (type.kind) {
        case SymbolKind::FixedSizeUnpackedArrayType: {
            auto& at = type.as<FixedSizeUnpackedArrayType>();
            buffer->format("[{}:{}]", at.range.left, at.range.right);
            break;
        }
        case SymbolKind::DynamicArrayType:
        case SymbolKind::DPIOpenArrayType:
            buffer->append("[]");
            break;
        case SymbolKind::AssociativeArrayType: {
            auto& at = type.as<AssociativeArrayType>();
            if (!at.indexType) {
                buffer->append("[*]");
            }
            else {
                buffer->append("[");
                at.indexType->visit(*this, ""sv);
                buffer->append("]");
            }
            break;
        }
        case SymbolKind::QueueType: {
            auto& at = type.as<QueueType>();
            if (at.maxBound)
                buffer->format("[$:{}]", at.maxBound);
            else
                buffer->append("[$]");
            break;
        }
        default:
            return;
    }

    // We can only reach this if we know we have an array type.
    printUnpackedArrayDim(type.getArrayElementType()->getCanonicalType());
}

void TypePrinter::printScope(const Scope* scope) {
    if (options.elideScopeNames)
        return;

    buffer->append(getLexicalPath(scope));
}

void TypePrinter::printAKA(const Type& type) {
    // Only print the AKA if the target type has a real name.
    // The typedefs can chain, so we want to walk down the chain
    // and take the last named type we see.
    const Type* target = &type;
    while (target->isAlias()) {
        const Type& newTarget = target->as<TypeAliasType>().targetType.getType();
        if (newTarget.name.empty() && !newTarget.isArray() && !newTarget.isVirtualInterface())
            break;

        target = &newTarget;
    }

    if (target != &type && target->name != type.name) {
        buffer->append(" (aka '");
        target->visit(*this, ""sv);
        buffer->append("')");
    }
}

TypeArgFormatter::TypeArgFormatter() {
    printer.options.addSingleQuotes = true;
    printer.options.elideScopeNames = true;
    printer.options.printAKA = true;
    printer.options.anonymousTypeStyle = TypePrintingOptions::FriendlyName;
}

void TypeArgFormatter::startMessage(const Diagnostic& diag) {
    seenTypes.clear();
    typesToDisambiguate.clear();

    SmallMap<std::string_view, const Type*, 4> typeNames;
    for (auto& arg : diag.args) {
        if (auto customArg = std::get_if<Diagnostic::CustomArgType>(&arg)) {
            if (auto typePtr = std::any_cast<const Type*>(&customArg->second)) {
                auto& type = **typePtr;
                if (type.isAlias()) {
                    auto [it, inserted] = typeNames.emplace(type.name, &type);
                    if (!inserted) {
                        typesToDisambiguate.insert(&type);
                        typesToDisambiguate.insert(it->second);
                    }
                }
            }
        }
    }
}

std::string TypeArgFormatter::format(const std::any& arg) {
    const Type& type = *std::any_cast<const Type*>(arg);
    bool unique = seenTypes.insert(&type).second;
    printer.options.printAKA = unique;
    printer.options.elideScopeNames = !type.isAlias() || !typesToDisambiguate.count(&type);

    printer.clear();
    printer.append(type);
    return printer.toString();
}

} // namespace slang::ast
