//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/MemberSymbols.h"

#include "PortBuilder.h"
#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/symbols/HierarchySymbols.h"
#include "slang/util/StackContainer.h"

namespace slang {

EmptyMemberSymbol& EmptyMemberSymbol::fromSyntax(Compilation& compilation,
                                                 const EmptyMemberSyntax& syntax) {
    auto result = compilation.emplace<EmptyMemberSymbol>(syntax.semi.location());
    compilation.addAttributes(*result, syntax.attributes);

    return *result;
}

const PackageSymbol* ExplicitImportSymbol::package() const {
    importedSymbol();
    return package_;
}

const Symbol* ExplicitImportSymbol::importedSymbol() const {
    if (!initialized) {
        initialized = true;

        const Scope* scope = getParentScope();
        ASSERT(scope);

        if (packageName.empty())
            return nullptr;

        package_ = scope->getCompilation().getPackage(packageName);
        if (!package_) {
            auto loc = location;
            if (auto syntax = getSyntax(); syntax)
                loc = syntax->as<PackageImportItemSyntax>().package.location();

            scope->addDiag(diag::UnknownPackage, loc) << packageName;
        }
        else if (importName.empty()) {
            return nullptr;
        }
        else {
            import = package_->find(importName);
            if (!import) {
                auto loc = location;
                if (auto syntax = getSyntax())
                    loc = syntax->as<PackageImportItemSyntax>().item.location();

                auto& diag = scope->addDiag(diag::UnknownPackageMember, loc);
                diag << importName << packageName;
            }
        }
    }
    return import;
}

void ExplicitImportSymbol::toJson(json& j) const {
    if (auto pkg = package())
        j["package"] = jsonLink(*pkg);

    if (auto sym = importedSymbol())
        j["import"] = jsonLink(*sym);
}

const PackageSymbol* WildcardImportSymbol::getPackage() const {
    if (!package) {
        const Scope* scope = getParentScope();
        ASSERT(scope);

        if (packageName.empty()) {
            package = nullptr;
        }
        else {
            package = scope->getCompilation().getPackage(packageName);
            if (!package.value()) {
                auto loc = location;
                if (auto syntax = getSyntax(); syntax)
                    loc = syntax->as<PackageImportItemSyntax>().package.location();

                scope->addDiag(diag::UnknownPackage, loc) << packageName;
            }
        }
    }
    return *package;
}

void WildcardImportSymbol::toJson(json& j) const {
    if (auto pkg = getPackage())
        j["package"] = jsonLink(*pkg);
}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort) :
    ValueSymbol(SymbolKind::Parameter, name, loc,
                DeclaredTypeFlags::InferImplicit | DeclaredTypeFlags::RequireConstant),
    isLocal(isLocal), isPort(isPort) {
}

void ParameterSymbol::fromSyntax(const Scope& scope, const ParameterDeclarationSyntax& syntax,
                                 bool isLocal, bool isPort,
                                 SmallVector<ParameterSymbol*>& results) {
    for (auto decl : syntax.declarators) {
        auto loc = decl->name.location();
        auto param = scope.getCompilation().emplace<ParameterSymbol>(decl->name.valueText(), loc,
                                                                     isLocal, isPort);
        param->setDeclaredType(*syntax.type);
        param->setFromDeclarator(*decl);

        if (!decl->initializer) {
            if (!isPort)
                scope.addDiag(diag::BodyParamNoInitializer, loc);
            else if (isLocal)
                scope.addDiag(diag::LocalParamNoInitializer, loc);
        }

        results.append(param);
    }
}

void ParameterSymbol::fromSyntax(const Scope& scope,
                                 const ParameterDeclarationStatementSyntax& syntax,
                                 SmallVector<ParameterSymbol*>& results) {
    auto& compilation = scope.getCompilation();
    fromSyntax(scope, *syntax.parameter, true, false, results);
    for (auto symbol : results)
        compilation.addAttributes(*symbol, syntax.attributes);
}

ParameterSymbol& ParameterSymbol::clone(Compilation& compilation) const {
    auto result = compilation.emplace<ParameterSymbol>(name, location, isLocal, isPort);
    if (auto syntax = getSyntax())
        result->setSyntax(*syntax);

    auto declared = getDeclaredType();
    result->getDeclaredType()->copyTypeFrom(*declared);

    if (auto init = declared->getInitializerSyntax())
        result->setInitializerSyntax(*init, declared->getInitializerLocation());

    if (declared->hasInitializer())
        result->setInitializer(*declared->getInitializer());

    result->overriden = overriden;
    return *result;
}

const ConstantValue& ParameterSymbol::getValue() const {
    return overriden ? *overriden : getConstantValue();
}

void ParameterSymbol::setValue(ConstantValue value) {
    auto scope = getParentScope();
    ASSERT(scope);
    overriden = scope->getCompilation().allocConstant(std::move(value));
}

void ParameterSymbol::toJson(json& j) const {
    j["value"] = getValue();
    j["isLocal"] = isLocalParam();
    j["isPort"] = isPortParam();
    j["isBody"] = isBodyParam();
}

PortSymbol::PortSymbol(string_view name, SourceLocation loc, bitmask<DeclaredTypeFlags> flags) :
    ValueSymbol(SymbolKind::Port, name, loc, flags) {
}

const Expression* PortSymbol::getConnection() const {
    if (!conn) {
        if (!connSyntax)
            conn = nullptr;
        else {
            BindContext context(*getParentScope(), LookupLocation::before(*this));
            auto loc = connSyntax->getFirstToken().location();

            switch (direction) {
                case PortDirection::In:
                    conn = &Expression::bind(getType(), *connSyntax, loc, context);
                    break;
                case PortDirection::Out:
                    // TODO: require assignable
                    // TODO: assignment-like context
                    conn = &Expression::bind(*connSyntax, context);
                    context.requireLValue(*conn.value(), loc);
                    break;
                case PortDirection::InOut:
                    // TODO: require assignable
                    // TODO: check not variable
                    conn = &Expression::bind(*connSyntax, context);
                    context.requireLValue(*conn.value(), loc);
                    break;
                case PortDirection::Ref:
                    // TODO: implement this
                    conn = nullptr;
                    break;
            }

            // TODO: if port is explicit, check that expression as well
        }
    }
    return *conn;
}

void PortSymbol::setConnection(const Expression* expr) {
    conn = expr;
    connSyntax = nullptr;
}

void PortSymbol::setConnection(const ExpressionSyntax& syntax) {
    conn = nullptr;
    connSyntax = &syntax;
}

void PortSymbol::fromSyntax(const PortListSyntax& syntax, const Scope& scope,
                            SmallVector<Symbol*>& results,
                            span<const PortDeclarationSyntax* const> portDeclarations) {
    switch (syntax.kind) {
        case SyntaxKind::AnsiPortList: {
            AnsiPortListBuilder builder{ scope };
            for (auto port : syntax.as<AnsiPortListSyntax>().ports) {
                switch (port->kind) {
                    case SyntaxKind::ImplicitAnsiPort:
                        results.append(builder.createPort(port->as<ImplicitAnsiPortSyntax>()));
                        break;
                    case SyntaxKind::ExplicitAnsiPort:
                        results.append(builder.createPort(port->as<ExplicitAnsiPortSyntax>()));
                        break;
                    default:
                        THROW_UNREACHABLE;
                }
            }

            if (!portDeclarations.empty()) {
                scope.addDiag(diag::PortDeclInANSIModule,
                              portDeclarations[0]->getFirstToken().location());
            }
            break;
        }
        case SyntaxKind::NonAnsiPortList: {
            NonAnsiPortListBuilder builder{ scope, portDeclarations };
            for (auto port : syntax.as<NonAnsiPortListSyntax>().ports) {
                switch (port->kind) {
                    case SyntaxKind::ImplicitNonAnsiPort:
                        results.append(builder.createPort(port->as<ImplicitNonAnsiPortSyntax>()));
                        break;
                    case SyntaxKind::ExplicitNonAnsiPort:
                        scope.addDiag(diag::NotYetSupported, port->sourceRange());
                        break;
                    default:
                        THROW_UNREACHABLE;
                }
            }
            break;
        }
        case SyntaxKind::WildcardPortList:
            scope.addDiag(diag::NotYetSupported, syntax.sourceRange());
            break;
        default:
            THROW_UNREACHABLE;
    }
}

void PortSymbol::makeConnections(const Scope& childScope, span<Symbol* const> ports,
                                 const SeparatedSyntaxList<PortConnectionSyntax>& portConnections) {
    const Scope* instanceScope = childScope.asSymbol().getParentScope();
    ASSERT(instanceScope);

    PortConnectionBuilder builder(childScope, *instanceScope, portConnections);
    for (auto portBase : ports) {
        if (portBase->kind == SymbolKind::Port)
            builder.setConnection(portBase->as<PortSymbol>());
        else
            builder.setConnection(portBase->as<InterfacePortSymbol>());
    }

    builder.finalize();
}

void PortSymbol::toJson(json& j) const {
    j["direction"] = toString(direction);

    if (internalSymbol)
        j["internalSymbol"] = jsonLink(*internalSymbol);

    if (defaultValue)
        j["default"] = *defaultValue;

    if (auto ext = getConnection())
        j["externalConnection"] = *ext;
}

span<const ConstantRange> InterfacePortSymbol::getDeclaredRange() const {
    if (range)
        return *range;

    auto syntax = getSyntax();
    ASSERT(syntax);

    auto scope = getParentScope();
    ASSERT(scope);

    BindContext context(*scope, LookupLocation::before(*this));

    SmallVectorSized<ConstantRange, 4> buffer;
    for (auto dimSyntax : syntax->as<DeclaratorSyntax>().dimensions) {
        EvaluatedDimension dim = context.evalDimension(*dimSyntax, true);
        if (!dim.isRange()) {
            buffer.clear();
            break;
        }

        buffer.append(dim.range);
    }

    range = buffer.copy(scope->getCompilation());
    return *range;
}

void InterfacePortSymbol::toJson(json& j) const {
    if (interfaceDef)
        j["interfaceDef"] = jsonLink(*interfaceDef);
    if (modport)
        j["modport"] = jsonLink(*modport);
    if (connection)
        j["connection"] = jsonLink(*connection);
}

void NetSymbol::fromSyntax(Compilation& compilation, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {

    // TODO: other net features
    const NetType& netType = compilation.getNetType(syntax.netType.kind);

    for (auto declarator : syntax.declarators) {
        auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                  declarator->name.location(), netType);

        net->setDeclaredType(*syntax.type, declarator->dimensions);
        net->setFromDeclarator(*declarator);
        results.append(net);
        compilation.addAttributes(*net, syntax.attributes);
    }
}

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                const Scope& scope, SmallVector<const ValueSymbol*>& results) {
    // TODO: check modifiers

    // This might actually be a net declaration with a user defined net type. That can only
    // be true if the data type syntax is a simple identifier, so if we see that it is,
    // perform a lookup and see what comes back.
    string_view simpleName = getSimpleTypeName(*syntax.type);
    if (!simpleName.empty()) {
        auto result = scope.lookupUnqualifiedName(simpleName, LookupLocation::max,
                                                  syntax.type->sourceRange());

        if (result && result->kind == SymbolKind::NetType) {
            const NetType& netType = result->as<NetType>();
            netType.getAliasTarget(); // force resolution of target

            auto& declaredType = *netType.getDeclaredType();
            for (auto declarator : syntax.declarators) {
                auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                          declarator->name.location(), netType);

                net->getDeclaredType()->copyTypeFrom(declaredType);
                net->setFromDeclarator(*declarator);
                results.append(net);
                compilation.addAttributes(*net, syntax.attributes);
            }
            return;
        }
    }

    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location());
        variable->setDeclaredType(*syntax.type);
        variable->setFromDeclarator(*declarator);
        results.append(variable);
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax,
                                           const VariableSymbol* lastVar) {
    auto var = compilation.emplace<VariableSymbol>(syntax.declarator->name.valueText(),
                                                   syntax.declarator->name.location());

    if (syntax.type)
        var->setDeclaredType(*syntax.type);
    else {
        ASSERT(lastVar);
        var->getDeclaredType()->copyTypeFrom(*lastVar->getDeclaredType());
    }

    var->setFromDeclarator(*syntax.declarator);
    return *var;
}

void VariableSymbol::toJson(json& j) const {
    j["lifetime"] = toString(lifetime);
    j["isConst"] = isConst;
}

void FormalArgumentSymbol::toJson(json& j) const {
    VariableSymbol::toJson(j);
    j["direction"] = toString(direction);
}

const Statement& SubroutineSymbol::getBody(EvalContext* evalContext) const {
    BindContext context(*this, LookupLocation::max);
    context.evalContext = evalContext;
    return binder.getStatement(context);
}

SubroutineSymbol& SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const FunctionDeclarationSyntax& syntax,
                                               const Scope& parent) {
    // TODO: non simple names?
    auto proto = syntax.prototype;
    Token nameToken = proto->name->getFirstToken();
    auto lifetime =
        SemanticFacts::getVariableLifetime(proto->lifetime).value_or(VariableLifetime::Automatic);

    auto subroutineKind = syntax.kind == SyntaxKind::TaskDeclaration ? SubroutineKind::Task
                                                                     : SubroutineKind::Function;
    auto result = compilation.emplace<SubroutineSymbol>(
        compilation, nameToken.valueText(), nameToken.location(), lifetime, subroutineKind, parent);

    result->setSyntax(syntax);
    compilation.addAttributes(*result, syntax.attributes);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto->portList) {
        const DataTypeSyntax* lastType = nullptr;
        auto lastDirection = FormalArgumentDirection::In;

        for (const FunctionPortSyntax* portSyntax : proto->portList->ports) {
            FormalArgumentDirection direction;
            bool directionSpecified = true;
            switch (portSyntax->direction.kind) {
                case TokenKind::InputKeyword:
                    direction = FormalArgumentDirection::In;
                    break;
                case TokenKind::OutputKeyword:
                    direction = FormalArgumentDirection::Out;
                    break;
                case TokenKind::InOutKeyword:
                    direction = FormalArgumentDirection::InOut;
                    break;
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
                declarator->name.valueText(), declarator->name.location(), direction);

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
    implicitReturnVar->isCompilerGenerated = true;
    result->addMember(*implicitReturnVar);
    result->returnValVar = implicitReturnVar;

    // TODO: mising return type
    result->arguments = arguments.copy(compilation);
    result->declaredReturnType.setTypeSyntax(*proto->returnType);
    result->binder.setItems(*result, syntax.items);
    return *result;
}

void SubroutineSymbol::toJson(json& j) const {
    j["returnType"] = getReturnType();
    j["defaultLifetime"] = toString(defaultLifetime);
    j["subroutineKind"] = subroutineKind;
}

ModportSymbol::ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Modport, name, loc), Scope(compilation, this) {
}

void ModportSymbol::fromSyntax(Compilation& compilation, const ModportDeclarationSyntax& syntax,
                               SmallVector<const ModportSymbol*>& results) {
    for (auto item : syntax.items) {
        // TODO: handle port list
        auto name = item->name;
        auto symbol =
            compilation.emplace<ModportSymbol>(compilation, name.valueText(), name.location());
        symbol->setSyntax(*item);
        compilation.addAttributes(*symbol, syntax.attributes);
        results.append(symbol);
    }
}

ContinuousAssignSymbol::ContinuousAssignSymbol(const ExpressionSyntax& syntax) :
    Symbol(SymbolKind::ContinuousAssign, "", syntax.getFirstToken().location()) {

    setSyntax(syntax);
}

ContinuousAssignSymbol::ContinuousAssignSymbol(SourceLocation loc, const Expression& assignment) :
    Symbol(SymbolKind::ContinuousAssign, "", loc), assign(&assignment) {
}

void ContinuousAssignSymbol::fromSyntax(Compilation& compilation,
                                        const ContinuousAssignSyntax& syntax,
                                        SmallVector<const ContinuousAssignSymbol*>& results) {
    for (auto expr : syntax.assignments) {
        auto symbol = compilation.emplace<ContinuousAssignSymbol>(*expr);
        compilation.addAttributes(*symbol, syntax.attributes);
        results.append(symbol);
    }
}

const Expression& ContinuousAssignSymbol::getAssignment() const {
    if (assign)
        return *assign;

    auto scope = getParentScope();
    ASSERT(scope);

    auto syntax = getSyntax();
    ASSERT(syntax);

    // Parser has ensured that this is a proper variable assignment expression here.
    assign = &Expression::bind(syntax->as<ExpressionSyntax>(),
                               BindContext(*scope, LookupLocation::before(*this)));
    return *assign;
}

void ContinuousAssignSymbol::toJson(json& j) const {
    j["assignment"] = getAssignment();
}

GenvarSymbol::GenvarSymbol(string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Genvar, name, loc) {
}

void GenvarSymbol::fromSyntax(Compilation& compilation, const GenvarDeclarationSyntax& syntax,
                              SmallVector<const GenvarSymbol*>& results) {
    for (auto id : syntax.identifiers) {
        auto name = id->identifier;
        if (name.valueText().empty())
            continue;

        auto genvar = compilation.emplace<GenvarSymbol>(name.valueText(), name.location());
        genvar->setSyntax(*id);
        compilation.addAttributes(*genvar, syntax.attributes);
        results.append(genvar);
    }
}

} // namespace slang
