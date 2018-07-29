//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "MemberSymbols.h"

#include <nlohmann/json.hpp>

#include "compilation/Compilation.h"
#include "symbols/HierarchySymbols.h"

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

void ParameterSymbol::fromSyntax(Compilation& compilation, const ParameterDeclarationSyntax& syntax,
                                 SmallVector<ParameterSymbol*>& results) {
    for (auto decl : syntax.declarators) {
        auto param = compilation.emplace<ParameterSymbol>(decl->name.valueText(), decl->name.location(), true, false);
        param->setDeclaredType(*syntax.type);
        if (decl->initializer)
            param->setDefault(*decl->initializer->expr);
        else
            compilation.addError(DiagCode::BodyParamNoInitializer, decl->name.location());

        results.append(param);
    }
}

ParameterSymbol& ParameterSymbol::fromDecl(Compilation& compilation, const Definition::ParameterDecl& decl) {
    auto param = compilation.emplace<ParameterSymbol>(decl.name, decl.location, decl.isLocal, decl.isPort);
    param->setDeclaredType(*decl.type);
    if (decl.initializer)
        param->setDefault(*decl.initializer);

    return *param;
}

std::tuple<const Type*, ConstantValue> ParameterSymbol::evaluate(const DataTypeSyntax& type,
                                                                 const ExpressionSyntax& expr,
                                                                 LookupLocation location,
                                                                 const Scope& scope) {
    // TODO: handle more cases here

    // If no type is given, infer the type from the initializer.
    Compilation& comp = scope.getCompilation();
    if (type.kind == SyntaxKind::ImplicitType) {
        const auto& bound = Expression::bind(comp, expr, BindContext(scope, location, BindFlags::Constant));
        return std::make_tuple(bound.type, bound.eval());
    }

    const Type& t = comp.getType(type, location, scope);
    const Expression& assignment = Expression::bind(comp, t, expr, expr.getFirstToken().location(),
                                                    BindContext(scope, location, BindFlags::Constant));

    return std::make_tuple(&t, assignment.eval());
}

const Type& ParameterSymbol::getType() const {
    // If we have no type set, compute and use the default type.
    if (!type.hasResult())
        getDefault();
    return type ? *type : ErrorType::Instance;
}

const ConstantValue& ParameterSymbol::getValue() const {
    // If we have no value set, compute and use the default value.
    if (!value)
        getDefault();
    return value ? *value : ConstantValue::Invalid;
}

void ParameterSymbol::setValue(ConstantValue newValue) {
    value = getScope()->getCompilation().createConstant(std::move(newValue));
}

const ConstantValue* ParameterSymbol::getDefault() const {
    if (!defaultValue)
        return nullptr;

    ASSERT(!evaluating);

    if (defaultValue.is<const ExpressionSyntax*>()) {
        ASSERT(declaredType);

        evaluating = true;
        const Scope* scope = getScope();
        auto typeAndValue = evaluate(*declaredType, *defaultValue.get<const ExpressionSyntax*>(),
                                     LookupLocation::before(*this), *scope);

        auto cv = scope->getCompilation().createConstant(std::move(std::get<1>(typeAndValue)));
        defaultValue = cv;
        evaluating = false;

        // If the value of this parameter hasn't yet been overriden, use the default type and value we just computed.
        if (!type.hasResult() || !value) {
            type = std::get<0>(typeAndValue);
            value = cv;
        }
    }

    return defaultValue.get<const ConstantValue*>();
}

void ParameterSymbol::setDefault(ConstantValue&& def) {
    ASSERT(!defaultValue);
    defaultValue = getScope()->getCompilation().createConstant(std::move(def));
}

void ParameterSymbol::setDefault(const ExpressionSyntax& syntax) {
    ASSERT(!defaultValue);
    defaultValue = &syntax;
}

void ParameterSymbol::toJson(json& j) const {
    j["type"] = getType();
    j["value"] = getValue();
    j["isLocal"] = isLocalParam();
    j["isPort"] = isPortParam();
    j["isBody"] = isBodyParam();
    if (hasDefault())
        j["default"] = *getDefault();
}

void NetSymbol::fromSyntax(Compilation& compilation, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {
    for (auto declarator : syntax.declarators) {
        auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                  declarator->name.location());
        
        // TODO: net types, initializers, etc
        net->dataType = *syntax.type;
        results.append(net);
    }
}

void NetSymbol::toJson(json& j) const {
    j["dataType"] = *dataType;
}

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                SmallVector<const VariableSymbol*>& results) {
    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location());
        variable->type = *syntax.type;
        if (declarator->initializer)
            variable->initializer = *declarator->initializer->expr;

        results.append(variable);
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax) {
    auto var = compilation.emplace<VariableSymbol>(syntax.declarator->name.valueText(),
                                                   syntax.declarator->name.location());
    var->type = *syntax.type;
    if (syntax.declarator->initializer)
        var->initializer = *syntax.declarator->initializer->expr;
    return *var;
}

void VariableSymbol::toJson(json& j) const {
    j["type"] = *type;
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

            if (declarator->initializer)
                arg->initializer = *declarator->initializer->expr;

            result->addMember(*arg);
            arguments.append(arg);
            lastDirection = direction;
        }
    }

    // The function gets an implicit variable inserted that represents the return value.
    // TODO: don't do this if returning void; also handle name collisions with this thing
    auto implicitReturnVar = compilation.emplace<VariableSymbol>(result->name, result->location);
    implicitReturnVar->type = *proto->returnType;
    result->addMember(*implicitReturnVar);
    result->returnValVar = implicitReturnVar;

    // TODO: mising return type
    result->arguments = arguments.copy(compilation);
    result->returnType = *proto->returnType;
    result->setBody(syntax.items);
    return *result;
}

void SubroutineSymbol::toJson(json& j) const {
    j["returnType"] = *returnType;
    j["defaultLifetime"] = defaultLifetime; // TODO: tostring
    j["isTask"] = isTask;
}

}
