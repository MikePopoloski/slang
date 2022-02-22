//------------------------------------------------------------------------------
// NetType.cpp
// Type class for nettypes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/types/NetType.h"

#include "slang/binding/BindContext.h"
#include "slang/compilation/Compilation.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/Scope.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/Type.h"

namespace slang {

NetType::NetType(NetKind netKind, string_view name, const Type& dataType) :
    Symbol(SymbolKind::NetType, name, SourceLocation()), declaredType(*this), netKind(netKind) {
    declaredType.setType(dataType);
}

NetType::NetType(string_view name, SourceLocation location) :
    Symbol(SymbolKind::NetType, name, location),
    declaredType(*this, DeclaredTypeFlags::UserDefinedNetType), netKind(UserDefined) {
}

const SubroutineSymbol* NetType::getResolutionFunction() const {
    if (resolver)
        return *resolver;

    auto syntax = getSyntax();
    auto scope = getParentScope();
    ASSERT(syntax && scope);

    auto& declSyntax = syntax->as<NetTypeDeclarationSyntax>();
    if (declSyntax.withFunction) {
        // TODO: lookup and validate the function here
    }

    resolver = nullptr;
    return *resolver;
}

void NetType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("type", getDataType());
}

NetType& NetType::fromSyntax(const Scope& scope, const NetTypeDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<NetType>(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    result->declaredType.setTypeSyntax(*syntax.type);

    return *result;
}

const NetType& NetType::getSimulatedNetType(const NetType& internal, const NetType& external,
                                            bool& shouldWarn) {
    shouldWarn = false;
    switch (internal.netKind) {
        case Unknown:
        case UserDefined:
            return internal;
        case Wire:
        case Tri:
            return external;
        case WAnd:
        case TriAnd:
            switch (external.netKind) {
                case Wire:
                case Tri:
                    return internal;
                case WOr:
                case TriOr:
                case TriReg:
                case Tri0:
                case Tri1:
                case UWire:
                    shouldWarn = true;
                    break;
                default:
                    break;
            }
            return external;
        case WOr:
        case TriOr:
            switch (external.netKind) {
                case Wire:
                case Tri:
                    return internal;
                case WAnd:
                case TriAnd:
                case TriReg:
                case Tri0:
                case Tri1:
                case UWire:
                    shouldWarn = true;
                    break;
                default:
                    break;
            }
            return external;
        case TriReg:
            switch (external.netKind) {
                case Wire:
                case Tri:
                    return internal;
                case WAnd:
                case TriAnd:
                case WOr:
                case TriOr:
                case UWire:
                    shouldWarn = true;
                    break;
                default:
                    break;
            }
            return external;
        case Tri0:
            switch (external.netKind) {
                case Wire:
                case Tri:
                case TriReg:
                    return internal;
                case WAnd:
                case TriAnd:
                case WOr:
                case TriOr:
                case UWire:
                case Tri1:
                    shouldWarn = true;
                    break;
                default:
                    break;
            }
            return external;
        case Tri1:
            switch (external.netKind) {
                case Wire:
                case Tri:
                case TriReg:
                    return internal;
                case WAnd:
                case TriAnd:
                case WOr:
                case TriOr:
                case UWire:
                case Tri0:
                    shouldWarn = true;
                    break;
                default:
                    break;
            }
            return external;
        case UWire:
            switch (external.netKind) {
                case UWire:
                case Supply0:
                case Supply1:
                    return external;
                case WAnd:
                case TriAnd:
                case WOr:
                case TriOr:
                case TriReg:
                case Tri0:
                case Tri1:
                    shouldWarn = true;
                    break;
                default:
                    break;
            }
            return internal;
        case Supply0:
            switch (external.netKind) {
                case Supply0:
                    return external;
                case Supply1:
                    shouldWarn = true;
                    return external;
                default:
                    break;
            }
            return internal;
        case Supply1:
            switch (external.netKind) {
                case Supply0:
                    shouldWarn = true;
                    return external;
                case Supply1:
                    return external;
                default:
                    break;
            }
            return internal;
        default:
            THROW_UNREACHABLE;
    }
}

} // namespace slang
