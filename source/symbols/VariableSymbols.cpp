//------------------------------------------------------------------------------
// VariableSymbols.cpp
// Contains variable-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/VariableSymbols.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Type.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"

namespace slang {

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                const Scope& scope, SmallVector<const ValueSymbol*>& results) {
    // This might actually be a net declaration with a user defined net type. That can only
    // be true if the data type syntax is a simple identifier, so if we see that it is,
    // perform a lookup and see what comes back.
    if (syntax.modifiers.empty()) {
        string_view simpleName = SyntaxFacts::getSimpleTypeName(*syntax.type);
        if (!simpleName.empty()) {
            auto result = Lookup::unqualified(scope, simpleName);
            if (result && result->kind == SymbolKind::NetType) {
                const NetType& netType = result->as<NetType>();
                netType.getAliasTarget(); // force resolution of target

                auto& declaredType = *netType.getDeclaredType();
                for (auto declarator : syntax.declarators) {
                    auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                              declarator->name.location(), netType);

                    net->getDeclaredType()->copyTypeFrom(declaredType);
                    net->setFromDeclarator(*declarator);
                    net->setAttributes(scope, syntax.attributes);
                    results.append(net);
                }
                return;
            }
        }
    }

    bool isConst = false;
    optional<VariableLifetime> lifetime;
    for (Token mod : syntax.modifiers) {
        switch (mod.kind) {
            case TokenKind::VarKeyword:
                break;
            case TokenKind::ConstKeyword:
                isConst = true;
                break;
            case TokenKind::StaticKeyword:
                // Static lifetimes are allowed in all contexts.
                lifetime = VariableLifetime::Static;
                break;
            case TokenKind::AutomaticKeyword:
                // Automatic lifetimes are only allowed in procedural contexts.
                lifetime = VariableLifetime::Automatic;
                if (!scope.isProceduralContext())
                    scope.addDiag(diag::AutomaticNotAllowed, mod.range());
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    // If no explicit lifetime is provided, find the default one for this scope.
    bool hasExplicitLifetime = lifetime.has_value();
    if (!hasExplicitLifetime)
        lifetime = scope.getDefaultLifetime();

    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location(), *lifetime);
        variable->isConstant = isConst;
        variable->setDeclaredType(*syntax.type);
        variable->setFromDeclarator(*declarator);
        variable->setAttributes(scope, syntax.attributes);
        results.append(variable);

        // If this is a static variable in a procedural context and it has an initializer,
        // the spec requires that the static keyword must be explicitly provided.
        if (*lifetime == VariableLifetime::Static && !hasExplicitLifetime &&
            declarator->initializer && scope.isProceduralContext()) {
            scope.addDiag(diag::StaticInitializerMustBeExplicit, declarator->name.range());
        }
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax,
                                           const VariableSymbol* lastVar) {
    auto nameToken = syntax.declarator->name;
    auto var = compilation.emplace<VariableSymbol>(nameToken.valueText(), nameToken.location(),
                                                   VariableLifetime::Automatic);

    if (syntax.type)
        var->setDeclaredType(*syntax.type);
    else {
        ASSERT(lastVar);
        var->getDeclaredType()->copyTypeFrom(*lastVar->getDeclaredType());
    }

    var->setFromDeclarator(*syntax.declarator);
    return *var;
}

VariableSymbol& VariableSymbol::fromForeachVar(Compilation& compilation,
                                               const IdentifierNameSyntax& syntax) {
    auto nameToken = syntax.identifier;
    auto var = compilation.emplace<VariableSymbol>(nameToken.valueText(), nameToken.location(),
                                                   VariableLifetime::Automatic);
    var->setSyntax(syntax);

    // TODO: for associative arrays the type needs to be the index type
    var->setType(compilation.getIntType());

    return *var;
}

void VariableSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("lifetime", toString(lifetime));
    serializer.write("isConstant", isConstant);
    serializer.write("isCompilerGenerated", isCompilerGenerated);
}

FormalArgumentSymbol::FormalArgumentSymbol(string_view name, SourceLocation loc,
                                           ArgumentDirection direction) :
    VariableSymbol(SymbolKind::FormalArgument, name, loc, VariableLifetime::Automatic),
    direction(direction) {
    if (direction == ArgumentDirection::ConstRef)
        isConstant = true;
}

void FormalArgumentSymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("direction", toString(direction));
}

void FieldSymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("offset", offset);
}

void NetSymbol::fromSyntax(const Scope& scope, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {

    // TODO: other net features
    auto& comp = scope.getCompilation();
    const NetType& netType = comp.getNetType(syntax.netType.kind);

    for (auto declarator : syntax.declarators) {
        auto net = comp.emplace<NetSymbol>(declarator->name.valueText(),
                                           declarator->name.location(), netType);

        net->setDeclaredType(*syntax.type, declarator->dimensions);
        net->setFromDeclarator(*declarator);
        net->setAttributes(scope, syntax.attributes);
        results.append(net);
    }
}

} // namespace slang