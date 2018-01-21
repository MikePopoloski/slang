//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "MemberSymbols.h"

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

const PackageSymbol* WildcardImportSymbol::getPackage() const {
    if (!package)
        package = getScope()->getCompilation().getPackage(packageName);
    return *package;
}

void ParameterSymbol::fromSyntax(Compilation& compilation, const ParameterDeclarationSyntax& syntax,
                                 SmallVector<ParameterSymbol*>& results) {
    for (auto decl : syntax.declarators) {
        auto param = compilation.emplace<ParameterSymbol>(decl->name.valueText(), decl->name.location(), true, false);
        param->setDeclaredType(syntax.type);
        if (decl->initializer)
            param->setDefault(decl->initializer->expr);
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
                                                                 const Scope& scope) {
    // TODO: handle more cases here

    // If no type is given, infer the type from the initializer.
    Compilation& comp = scope.getCompilation();
    if (type.kind == SyntaxKind::ImplicitType) {
        const auto& bound = comp.bindExpression(expr, scope);
        return std::make_tuple(bound.type, bound.eval());
    }

    const Type& t = comp.getType(type, scope);
    const Expression& assignment = comp.bindAssignment(t, expr, scope, expr.getFirstToken().location());

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

    if (defaultValue.is<const ExpressionSyntax*>()) {
        ASSERT(declaredType);

        const Scope* scope = getScope();
        auto typeAndValue = evaluate(*declaredType, *defaultValue.get<const ExpressionSyntax*>(), *scope);
        auto cv = scope->getCompilation().createConstant(std::move(std::get<1>(typeAndValue)));
        defaultValue = cv;

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

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                SmallVector<const VariableSymbol*>& results) {
    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location());
        variable->type = syntax.type;
        if (declarator->initializer)
            variable->initializer = declarator->initializer->expr;

        results.append(variable);
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax) {
    auto var = compilation.emplace<VariableSymbol>(syntax.declarator.name.valueText(),
                                                   syntax.declarator.name.location());
    var->type = syntax.type;
    if (syntax.declarator.initializer)
        var->initializer = syntax.declarator.initializer->expr;
    return *var;
}

SubroutineSymbol& SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const FunctionDeclarationSyntax& syntax) {
    // TODO: non simple names?
    const auto& proto = syntax.prototype;
    Token nameToken = proto.name.getFirstToken();

    auto result = compilation.emplace<SubroutineSymbol>(
        compilation,
        nameToken.valueText(),
        nameToken.location(),
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
                default:
                    THROW_UNREACHABLE;
            }

            const auto& declarator = portSyntax->declarator;
            auto arg = compilation.emplace<FormalArgumentSymbol>(
                declarator.name.valueText(),
                declarator.name.location(),
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
