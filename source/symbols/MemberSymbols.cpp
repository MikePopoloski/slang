//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "binding/Binder.h"
#include "compilation/Compilation.h"

namespace slang {

const PackageSymbol* ExplicitImportSymbol::package() const {
    importedSymbol();
    return package_;
}

const Symbol* ExplicitImportSymbol::importedSymbol() const {
    if (!initialized) {
        initialized = true;

        package_ = getScope()->getCompilation().getPackage(packageName);
        // TODO: errors
        if (package_)
            import = package_->lookupDirect(importName);
    }
    return import;
}

const PackageSymbol* WildcardImportSymbol::getPackage() const {
    if (!package)
        package = getScope()->getCompilation().getPackage(packageName);
    return *package;
}

void ParameterSymbol::fromSyntax(Compilation& compilation, const ParameterDeclarationSyntax& syntax,
                                 SmallVector<ParameterSymbol*>& results) {

    bool isLocal = syntax.keyword.kind == TokenKind::LocalParamKeyword;

    for (const VariableDeclaratorSyntax* decl : syntax.declarators) {
        auto param = compilation.emplace<ParameterSymbol>(decl->name.valueText());
        param->isLocalParam = isLocal;

        if (decl->initializer) {
            param->defaultValue = decl->initializer->expr;
            param->value = param->defaultValue;
        }

        // TODO: handle defaultType

            // TODO:
           /* else if (local)
                addError(DiagCode::LocalParamNoInitializer, declLocation);
            else if (bodyParam)
                addError(DiagCode::BodyParamNoInitializer, declLocation);*/

        results.append(param);
    }
}

// TODO:
//void ParameterSymbol::evaluate(const ExpressionSyntax* expr, const Type*& determinedType,
//                               ConstantValue*& determinedValue, const Scope& scope) const {
//    ASSERT(expr);
//
//    // If no type is given, infer the type from the initializer
//    if (typeSyntax->kind == SyntaxKind::ImplicitType) {
//        const auto& bound = Binder(scope).bindConstantExpression(*expr);
//        determinedType = bound.type;
//        if (!bound.bad())
//            determinedValue = getRoot().constantAllocator.emplace(bound.eval());
//    }
//    else {
//        determinedType = &getRoot().compilation.getType(*typeSyntax, scope);
//        determinedValue = getRoot().constantAllocator.emplace(scope.evaluateConstantAndConvert(*expr, *determinedType, location));
//    }
//}

//VariableSymbol::VariableSymbol(string_view name, const Scope& parent,
//                               VariableLifetime lifetime, bool isConst) :
//    Symbol(SymbolKind::Variable, parent, name),
//    type(&parent), initializer(&parent),
//    lifetime(lifetime), isConst(isConst) {}

//VariableSymbol::VariableSymbol(SymbolKind kind, string_view name, const Scope& parent,
//                               VariableLifetime lifetime, bool isConst) :
//    Symbol(kind, parent, name),
//    type(&parent), initializer(&parent),
//    lifetime(lifetime), isConst(isConst) {}

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                SmallVector<const VariableSymbol*>& results) {
    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText());
        variable->type = syntax.type;
        if (declarator->initializer)
            variable->initializer = declarator->initializer->expr;

        results.append(variable);
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax) {
    auto var = compilation.emplace<VariableSymbol>(syntax.declarator.name.valueText());
    var->type = syntax.type;
    if (syntax.declarator.initializer)
        var->initializer = syntax.declarator.initializer->expr;
    return *var;
}

SubroutineSymbol& SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const FunctionDeclarationSyntax& syntax) {
    // TODO: non simple names?
    const auto& proto = syntax.prototype;
    auto result = compilation.emplace<SubroutineSymbol>(
        compilation,
        proto.name.getFirstToken().valueText(),
        SemanticFacts::getVariableLifetime(proto.lifetime).value_or(VariableLifetime::Automatic),
        syntax.kind == SyntaxKind::TaskDeclaration
    );

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto.portList) {
        const DataTypeSyntax* lastType = nullptr;
        auto lastDirection = FormalArgumentDirection::In;

        for (const FunctionPortSyntax* portSyntax : proto.portList->ports) {
            FormalArgumentDirection direction;
            bool directionSpecified = true;
            switch (portSyntax->direction.kind) {
                case TokenKind::InputKeyword: direction = FormalArgumentDirection::In; break;
                case TokenKind::OutputKeyword: direction = FormalArgumentDirection::Out; break;
                case TokenKind::InOutKeyword: direction = FormalArgumentDirection::InOut; break;
                case TokenKind::RefKeyword:
                    if (portSyntax->constKeyword)
                        direction = FormalArgumentDirection::ConstRef;
                    else
                        direction = FormalArgumentDirection::Ref;
                    break;
                case TokenKind::Unknown:
                    // Otherwise, we "inherit" the previous argument
                    direction = lastDirection;
                    directionSpecified = false;
                    break;
                default: THROW_UNREACHABLE;
            }

            const auto& declarator = portSyntax->declarator;
            auto arg = compilation.emplace<FormalArgumentSymbol>(declarator.name.valueText(), direction);

            // If we're given a type, use that. Otherwise, if we were given a
            // direction, default to logic. Otherwise, use the last type.
            if (portSyntax->dataType) {
                arg->type = *portSyntax->dataType;
                lastType = portSyntax->dataType;
            }
            else if (directionSpecified || !lastType) {
                arg->type = compilation.getLogicType();
                lastType = nullptr;
            }
            else {
                arg->type = *lastType;
            }

            if (declarator.initializer)
                arg->initializer = declarator.initializer->expr;

            result->addMember(*arg);
            arguments.append(arg);
            lastDirection = direction;
        }
    }

    // TODO: mising return type
    result->arguments = arguments.copy(compilation);
    result->returnType = *proto.returnType;
    result->setBody(syntax.items);
    return *result;
}

}
