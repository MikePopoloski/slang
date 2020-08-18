//------------------------------------------------------------------------------
// ClassSymbols.cpp
// Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/ClassSymbols.h"

#include "slang/compilation/Compilation.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

ClassPropertySymbol::ClassPropertySymbol(string_view name, SourceLocation loc,
                                         VariableLifetime lifetime, Visibility visibility) :
    VariableSymbol(SymbolKind::ClassProperty, name, loc, lifetime),
    visibility(visibility) {
}

void ClassPropertySymbol::fromSyntax(const Scope& scope,
                                     const ClassPropertyDeclarationSyntax& syntax,
                                     SmallVector<const ClassPropertySymbol*>& results) {
    auto& comp = scope.getCompilation();
    auto& dataSyntax = syntax.declaration->as<DataDeclarationSyntax>();

    bool isConst = false;
    VariableLifetime lifetime = VariableLifetime::Automatic;
    Visibility visibility = Visibility::Public;

    for (Token qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::ConstKeyword:
                isConst = true;
                break;
            case TokenKind::StaticKeyword:
                lifetime = VariableLifetime::Static;
                break;
            case TokenKind::LocalKeyword:
                visibility = Visibility::Local;
                break;
            case TokenKind::ProtectedKeyword:
                visibility = Visibility::Protected;
                break;
            case TokenKind::RandKeyword:
            case TokenKind::RandCKeyword:
                scope.addDiag(diag::NotYetSupported, qual.range());
                break;
            case TokenKind::PureKeyword:
            case TokenKind::VirtualKeyword:
            case TokenKind::ExternKeyword:
                // These are not allowed on properties; the parser will issue a diagnostic
                // so just ignore them here.
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    for (Token mod : dataSyntax.modifiers) {
        switch (mod.kind) {
            case TokenKind::VarKeyword:
            case TokenKind::AutomaticKeyword:
                break;
            case TokenKind::ConstKeyword:
                isConst = true;
                break;
            case TokenKind::StaticKeyword:
                lifetime = VariableLifetime::Static;
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    for (auto declarator : dataSyntax.declarators) {
        auto var = comp.emplace<ClassPropertySymbol>(
            declarator->name.valueText(), declarator->name.location(), lifetime, visibility);
        var->isConstant = isConst;
        var->setDeclaredType(*dataSyntax.type);
        var->setFromDeclarator(*declarator);
        var->setAttributes(scope, syntax.attributes);
        results.append(var);
    }
}

void ClassPropertySymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("visibility", toString(visibility));
}

ClassType::ClassType(Compilation& compilation, string_view name, SourceLocation loc) :
    Type(SymbolKind::ClassType, name, loc), Scope(compilation, this) {
}

ConstantValue ClassType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

const Type& ClassType::fromSyntax(const Scope& scope, const ClassDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    if (syntax.virtualOrInterface) {
        // TODO: support this
        scope.addDiag(diag::NotYetSupported, syntax.virtualOrInterface.range());
        return comp.getErrorType();
    }

    auto result = comp.emplace<ClassType>(comp, syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    for (auto member : syntax.items)
        result->addMembers(*member);

    // TODO: parameters
    // TODO: extends
    // TODO: implements
    // TODO: lifetime

    return *result;
}

} // namespace slang
