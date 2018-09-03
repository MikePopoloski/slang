//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/MemberSymbols.h"

#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/symbols/HierarchySymbols.h"

namespace slang {

const PackageSymbol* ExplicitImportSymbol::package() const {
    importedSymbol();
    return package_;
}

const Symbol* ExplicitImportSymbol::importedSymbol() const {
    if (!initialized) {
        initialized = true;

        package_ = getScope()->getCompilation().getPackage(packageName);
        // TODO: errors, explicit imports, transparent members?
        if (package_)
            import = package_->find(importName);
    }
    return import;
}

void ExplicitImportSymbol::toJson(json& j) const {
    j["package"] = std::string(packageName);
}

const PackageSymbol* WildcardImportSymbol::getPackage() const {
    if (!package)
        package = getScope()->getCompilation().getPackage(packageName);
    return *package;
}

void WildcardImportSymbol::toJson(json& j) const {
    j["package"] = std::string(packageName);
}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort) :
    ValueSymbol(SymbolKind::Parameter, name, loc, DeclaredTypeFlags::AllowImplicit | DeclaredTypeFlags::RequireConstant),
    isLocal(isLocal), isPort(isPort)
{
}

void ParameterSymbol::fromSyntax(Compilation& compilation, const ParameterDeclarationSyntax& syntax,
                                 bool isLocal, bool isPort, SmallVector<ParameterSymbol*>& results) {
    for (auto decl : syntax.declarators) {
        auto loc = decl->name.location();
        auto param = compilation.emplace<ParameterSymbol>(decl->name.valueText(), loc, isLocal, isPort);
        param->setDeclaredType(*syntax.type);
        param->setFromDeclarator(*decl);

        if (!decl->initializer) {
            if (!isPort)
                compilation.addError(*param, DiagCode::BodyParamNoInitializer, loc);
            else if (isLocal)
                compilation.addError(*param, DiagCode::LocalParamNoInitializer, loc);
        }

        param->setSyntax(*decl);
        results.append(param);
    }
}

ParameterSymbol& ParameterSymbol::createOverride(Compilation& compilation, const Expression* newInitializer) const {
    auto result = compilation.emplace<ParameterSymbol>(name, location, isLocal, isPort);
    if (auto syntax = getSyntax())
        result->setSyntax(*syntax);

    auto declared = getDeclaredType();
    if (auto typeSyntax = declared->getTypeSyntax()) {
        if (auto dimensions = declared->getDimensionSyntax())
            result->setDeclaredType(*typeSyntax, *dimensions);
        else
            result->setDeclaredType(*typeSyntax);
    }

    if (newInitializer) {
        result->setType(*newInitializer->type);
        result->setInitializer(*newInitializer);
    }
    else if (auto init = declared->getInitializerSyntax()) {
        result->setInitializerSyntax(*init, declared->getInitializerLocation());
    }

    return *result;
}

const ConstantValue& ParameterSymbol::getValue() const {
    return overriden ? *overriden : getConstantValue();
}

void ParameterSymbol::setValue(ConstantValue value) {
    auto scope = getScope();
    ASSERT(scope);
    overriden = scope->getCompilation().createConstant(std::move(value));
}

void ParameterSymbol::toJson(json& j) const {
    j["type"] = getType();
    j["value"] = getValue();
    j["isLocal"] = isLocalParam();
    j["isPort"] = isPortParam();
    j["isBody"] = isBodyParam();
}

void NetSymbol::fromSyntax(Compilation& compilation, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {
    for (auto declarator : syntax.declarators) {
        auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                  declarator->name.location());

        // TODO: net types, initializers, etc
        net->setDeclaredType(*syntax.type, declarator->dimensions);
        net->setSyntax(*declarator);
        results.append(net);
    }
}

void NetSymbol::toJson(json&) const {
    // TODO:
    //j["dataType"] = *dataType;
}

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                SmallVector<const VariableSymbol*>& results) {
    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location());
        variable->setDeclaredType(*syntax.type);
        variable->setFromDeclarator(*declarator);
        variable->setSyntax(*declarator);
        results.append(variable);
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax) {
    auto var = compilation.emplace<VariableSymbol>(syntax.declarator->name.valueText(),
                                                   syntax.declarator->name.location());
    var->setDeclaredType(*syntax.type);
    var->setFromDeclarator(*syntax.declarator);
    var->setSyntax(*syntax.declarator);
    return *var;
}

void VariableSymbol::toJson(json& j) const {
    j["type"] = getType();
    j["lifetime"] = lifetime; // TODO: tostring
    j["isConst"] = isConst;

    // TODO:
    //if (initializer)
    //    j["initializer"] =
}

void FormalArgumentSymbol::toJson(json& j) const {
    VariableSymbol::toJson(j);
    j["direction"] = direction; // TODO: tostring
}

SubroutineSymbol& SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const FunctionDeclarationSyntax& syntax,
                                               const Scope& parent) {
    // TODO: non simple names?
    auto proto = syntax.prototype;
    Token nameToken = proto->name->getFirstToken();

    auto result = compilation.emplace<SubroutineSymbol>(
        compilation,
        nameToken.valueText(),
        nameToken.location(),
        SemanticFacts::getVariableLifetime(proto->lifetime).value_or(VariableLifetime::Automatic),
        syntax.kind == SyntaxKind::TaskDeclaration,
        parent
    );
    result->setSyntax(syntax);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto->portList) {
        const DataTypeSyntax* lastType = nullptr;
        auto lastDirection = FormalArgumentDirection::In;

        for (const FunctionPortSyntax* portSyntax : proto->portList->ports) {
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
                default:
                    THROW_UNREACHABLE;
            }

            auto declarator = portSyntax->declarator;
            auto arg = compilation.emplace<FormalArgumentSymbol>(
                declarator->name.valueText(),
                declarator->name.location(),
                direction
            );
            arg->setSyntax(*portSyntax);

            // If we're given a type, use that. Otherwise, if we were given a
            // direction, default to logic. Otherwise, use the last type.
            if (portSyntax->dataType) {
                arg->setDeclaredType(*portSyntax->dataType);
                lastType = portSyntax->dataType;
            }
            else if (directionSpecified || !lastType) {
                arg->setType(compilation.getLogicType());
                lastType = nullptr;
            }
            else {
                arg->setDeclaredType(*lastType);
            }

            arg->setFromDeclarator(*declarator);

            result->addMember(*arg);
            arguments.append(arg);
            lastDirection = direction;
        }
    }

    // The function gets an implicit variable inserted that represents the return value.
    // TODO: don't do this if returning void; also handle name collisions with this thing
    auto implicitReturnVar = compilation.emplace<VariableSymbol>(result->name, result->location);
    implicitReturnVar->setDeclaredType(*proto->returnType);
    result->addMember(*implicitReturnVar);
    result->returnValVar = implicitReturnVar;

    // TODO: mising return type
    result->arguments = arguments.copy(compilation);
    result->declaredReturnType.setTypeSyntax(*proto->returnType);
    result->setBody(syntax.items);
    return *result;
}

void SubroutineSymbol::toJson(json& j) const {
    j["returnType"] = getReturnType();
    j["defaultLifetime"] = defaultLifetime; // TODO: tostring
    j["isTask"] = isTask;
}

}
