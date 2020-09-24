//------------------------------------------------------------------------------
// ClassSymbols.cpp
// Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/ClassSymbols.h"

#include "ParameterBuilder.h"

#include "slang/binding/AssignmentExpressions.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/AllTypes.h"
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

        if (isConst && lifetime == VariableLifetime::Static && !declarator->initializer)
            scope.addDiag(diag::StaticConstNoInitializer, declarator->name.range());
    }
}

void ClassPropertySymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("visibility", toString(visibility));
}

ClassMethodPrototypeSymbol::ClassMethodPrototypeSymbol(Compilation& compilation, string_view name,
                                                       SourceLocation loc,
                                                       SubroutineKind subroutineKind,
                                                       Visibility visibility,
                                                       bitmask<MethodFlags> flags) :
    Symbol(SymbolKind::ClassMethodPrototype, name, loc),
    Scope(compilation, this), declaredReturnType(*this), subroutineKind(subroutineKind),
    visibility(visibility), flags(flags) {
}

ClassMethodPrototypeSymbol& ClassMethodPrototypeSymbol::fromSyntax(
    const Scope& scope, const ClassMethodPrototypeSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto& proto = *syntax.prototype;

    Visibility visibility = Visibility::Public;
    bitmask<MethodFlags> flags;
    Token nameToken = proto.name->getLastToken();
    auto subroutineKind = proto.keyword.kind == TokenKind::TaskKeyword ? SubroutineKind::Task
                                                                       : SubroutineKind::Function;

    for (Token qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::LocalKeyword:
                visibility = Visibility::Local;
                break;
            case TokenKind::ProtectedKeyword:
                visibility = Visibility::Protected;
                break;
            case TokenKind::StaticKeyword:
                flags |= MethodFlags::Static;
                break;
            case TokenKind::PureKeyword:
                flags |= MethodFlags::Pure;
                break;
            case TokenKind::VirtualKeyword:
                flags |= MethodFlags::Virtual;
                break;
            case TokenKind::ConstKeyword:
            case TokenKind::ExternKeyword:
            case TokenKind::RandKeyword:
                // Parser already issued errors for these, so just ignore them here.
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    if (nameToken.valueText() == "new")
        flags |= MethodFlags::Constructor;

    auto result = comp.emplace<ClassMethodPrototypeSymbol>(
        comp, nameToken.valueText(), nameToken.location(), subroutineKind, visibility, flags);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    if (subroutineKind == SubroutineKind::Function)
        result->declaredReturnType.setTypeSyntax(*proto.returnType);
    else
        result->declaredReturnType.setType(comp.getVoidType());

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto.portList) {
        SubroutineSymbol::buildArguments(*result, *proto.portList, VariableLifetime::Automatic,
                                         arguments);
    }

    result->arguments = arguments.copy(comp);
    return *result;
}

const SubroutineSymbol* ClassMethodPrototypeSymbol::getSubroutine() const {
    if (subroutine)
        return *subroutine;

    // The out-of-block definition must be in our class's parent scope.
    ASSERT(getParentScope() && getParentScope()->asSymbol().getParentScope());
    auto& classType = getParentScope()->asSymbol();
    auto& scope = *classType.getParentScope();

    auto& comp = scope.getCompilation();
    auto [syntax, index] = comp.findOutOfBlockMethod(scope, classType.name, name);
    if (!syntax) {
        scope.addDiag(diag::NoMethodImplFound, location) << name;
        subroutine = nullptr;
        return nullptr;
    }

    // The method definition must be located after the class definition.
    if (index <= classType.getIndex()) {
        auto& diag = scope.addDiag(diag::MethodDefinitionBeforeClass,
                                   syntax->prototype->name->getLastToken().location());
        diag << name << classType.name;
        diag.addNote(diag::NoteDeclarationHere, classType.location);
    }

    subroutine =
        &SubroutineSymbol::createOutOfBlock(comp, *syntax, *this, *getParentScope(), scope, index);
    return *subroutine;
}

void ClassMethodPrototypeSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("returnType", getReturnType());
    serializer.write("subroutineKind", toString(subroutineKind));
    serializer.write("visibility", toString(visibility));

    serializer.startArray("arguments");
    for (auto const arg : arguments) {
        arg->serializeTo(serializer);
    }
    serializer.endArray();
}

void ClassType::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void ClassType::checkForwardDecls() const {
    if (firstForward)
        firstForward->checkType(ForwardingTypedefSymbol::Class, Visibility::Public, location);
}

ClassType::ClassType(Compilation& compilation, string_view name, SourceLocation loc) :
    Type(SymbolKind::ClassType, name, loc), Scope(compilation, this) {
}

ConstantValue ClassType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

const Symbol& ClassType::fromSyntax(const Scope& scope, const ClassDeclarationSyntax& syntax) {
    // If this class declaration has parameter ports it's actually a generic class definition.
    // Create that now and wait until someone specializes it in order to get an actual type.
    if (syntax.parameters && !syntax.parameters->declarations.empty())
        return GenericClassDefSymbol::fromSyntax(scope, syntax);

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ClassType>(comp, syntax.name.valueText(), syntax.name.location());
    return result->populate(scope, syntax);
}

const Type& ClassType::populate(const Scope& scope, const ClassDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    if (syntax.virtualOrInterface) {
        // TODO: support this
        scope.addDiag(diag::NotYetSupported, syntax.virtualOrInterface.range());
        return comp.getErrorType();
    }

    setSyntax(syntax);
    for (auto member : syntax.items)
        addMembers(*member);

    if (syntax.extendsClause || syntax.implementsClause)
        setNeedElaboration();

    return *this;
}

void ClassType::inheritMembers(function_ref<void(const Symbol&)> insertCB) const {
    auto syntax = getSyntax();
    ASSERT(syntax);

    auto& classSyntax = syntax->as<ClassDeclarationSyntax>();
    if (!classSyntax.extendsClause)
        return;

    auto scope = getParentScope();
    ASSERT(scope);

    // Find the class type named as the base class.
    BindContext context(*scope, LookupLocation::before(*this));
    auto baseType = Lookup::findClass(*classSyntax.extendsClause->baseName, context);
    if (!baseType)
        return;

    // Inherit all base class members that don't conflict with our declared symbols.
    const Symbol* baseConstructor = nullptr;
    auto& comp = scope->getCompilation();
    auto& scopeNameMap = getNameMap();
    for (auto& member : baseType->members()) {
        if (member.name.empty())
            continue;

        // Don't inherit if the member is already overriden.
        if (auto it = scopeNameMap.find(member.name); it != scopeNameMap.end())
            continue;

        // Don't inherit constructors.
        if (member.kind == SymbolKind::Subroutine &&
            (member.as<SubroutineSymbol>().flags & MethodFlags::Constructor) != 0) {
            baseConstructor = &member;
            continue;
        }

        // If the symbol itself was already inherited, create a new wrapper around
        // it for our own scope.
        const Symbol* toWrap = &member;
        if (member.kind == SymbolKind::TransparentMember)
            toWrap = &member.as<TransparentMemberSymbol>().wrapped;

        // All symbols get inserted into the beginning of the scope using the
        // provided insertion callback. We insert them as TransparentMemberSymbols
        // so that we can trace a path back to the actual location they are declared.
        auto wrapper = comp.emplace<TransparentMemberSymbol>(*toWrap);
        insertCB(*wrapper);
    }

    // Assign this before resolving the constructor call below.
    baseClass = baseType;

    // If we have a constructor, find whether it invokes super.new in its body.
    if (auto ourConstructor = find("new")) {
        auto checkForSuperNew = [&](const Statement& stmt) {
            if (stmt.kind == StatementKind::ExpressionStatement) {
                auto& expr = stmt.as<ExpressionStatement>().expr;
                if (expr.kind == ExpressionKind::NewClass &&
                    expr.as<NewClassExpression>().isSuperClass) {
                    baseConstructorCall = &expr;
                }
            }
        };

        auto& body = ourConstructor->as<SubroutineSymbol>().getBody();
        if (body.kind != StatementKind::List)
            checkForSuperNew(body);
        else {
            for (auto stmt : body.as<StatementList>().list) {
                if (stmt->kind != StatementKind::VariableDeclaration) {
                    checkForSuperNew(*stmt);
                    break;
                }
            }
        }
    }

    if (auto extendsArgs = classSyntax.extendsClause->arguments) {
        // Can't have both a super.new and extends arguments.
        if (baseConstructorCall) {
            auto& diag =
                scope->addDiag(diag::BaseConstructorDuplicate, baseConstructorCall->sourceRange);
            diag.addNote(diag::NotePreviousUsage, extendsArgs->getFirstToken().location());
            return;
        }

        // If we have a base class constructor, create the call to it.
        if (baseConstructor) {
            SourceRange range = classSyntax.extendsClause->sourceRange();
            Lookup::ensureVisible(*baseConstructor, context, range);

            baseConstructorCall =
                &CallExpression::fromArgs(comp, &baseConstructor->as<SubroutineSymbol>(), nullptr,
                                          extendsArgs, range, context);
        }
        else if (!extendsArgs->parameters.empty()) {
            auto& diag = context.addDiag(diag::TooManyArguments, extendsArgs->sourceRange());
            diag << 0;
            diag << extendsArgs->parameters.size();
        }
    }

    // If we have a base class constructor and nothing called it, make sure
    // it has no arguments or all of the arguments have default values.
    if (baseConstructor && !baseConstructorCall) {
        for (auto arg : baseConstructor->as<SubroutineSymbol>().arguments) {
            if (!arg->getInitializer()) {
                auto& diag = scope->addDiag(diag::BaseConstructorNotCalled,
                                            classSyntax.extendsClause->sourceRange());
                diag << name << baseClass->name;
                diag.addNote(diag::NoteDeclarationHere, baseConstructor->location);
                return;
            }
        }

        Lookup::ensureVisible(*baseConstructor, context, classSyntax.extendsClause->sourceRange());
    }
}

void ClassType::serializeTo(ASTSerializer& serializer) const {
    if (firstForward)
        serializer.write("forward", *firstForward);
    if (genericClass)
        serializer.writeLink("genericClass", *genericClass);
}

const Symbol& GenericClassDefSymbol::fromSyntax(const Scope& scope,
                                                const ClassDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.allocGenericClass(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);

    // Extract information about parameters and save it for later use
    // when building specializations.
    ASSERT(syntax.parameters);
    ParameterBuilder::createDecls(scope, *syntax.parameters, result->paramDecls);

    return *result;
}

const Type* GenericClassDefSymbol::getDefaultSpecialization(Compilation& compilation) const {
    if (defaultSpecialization)
        return *defaultSpecialization;

    auto result = getSpecializationImpl(compilation, LookupLocation::max, location,
                                        /* forceInvalidParams */ false, nullptr);
    defaultSpecialization = result;
    return result;
}

const Type& GenericClassDefSymbol::getSpecialization(
    Compilation& compilation, LookupLocation lookupLocation,
    const ParameterValueAssignmentSyntax& syntax) const {

    auto result =
        getSpecializationImpl(compilation, lookupLocation, syntax.getFirstToken().location(),
                              /* forceInvalidParams */ false, &syntax);
    if (!result)
        return compilation.getErrorType();

    return *result;
}

const Type& GenericClassDefSymbol::getInvalidSpecialization(Compilation& compilation) const {
    auto result = getSpecializationImpl(compilation, LookupLocation::max, location,
                                        /* forceInvalidParams */ true, nullptr);
    if (!result)
        return compilation.getErrorType();

    return *result;
}

const Type* GenericClassDefSymbol::getSpecializationImpl(
    Compilation& compilation, LookupLocation lookupLocation, SourceLocation instanceLoc,
    bool forceInvalidParams, const ParameterValueAssignmentSyntax* syntax) const {

    auto scope = getParentScope();
    ASSERT(scope);

    // Create a class type instance to hold the parameters. If it turns out we already
    // have this specialization cached we'll throw it away, but that's not a big deal.
    auto classType = compilation.emplace<ClassType>(compilation, name, location);
    classType->genericClass = this;
    classType->setParent(*scope, getIndex());

    ParameterBuilder paramBuilder(*scope, name, paramDecls);
    if (syntax)
        paramBuilder.setAssignments(*syntax);

    // If this is for the default specialization, `syntax` will be null.
    // We want to suppress errors about params not having values and just
    // return null so that the caller can figure out if this is actually a problem.
    bool isForDefault = syntax == nullptr;
    if (!paramBuilder.createParams(*classType, lookupLocation, instanceLoc, forceInvalidParams,
                                   isForDefault)) {
        if (isForDefault)
            return nullptr;

        // Otherwise use an error type instead.
        return &compilation.getErrorType();
    }

    SpecializationKey key(*this, paramBuilder.paramValues.copy(compilation),
                          paramBuilder.typeParams.copy(compilation));
    if (auto it = specMap.find(key); it != specMap.end())
        return it->second;

    // Not found, so this is a new entry. Fill in its members and store the
    // specialization for later lookup.
    const Type& result = classType->populate(*scope, getSyntax()->as<ClassDeclarationSyntax>());
    specMap.emplace(key, &result);
    return &result;
}

void GenericClassDefSymbol::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void GenericClassDefSymbol::checkForwardDecls() const {
    if (firstForward)
        firstForward->checkType(ForwardingTypedefSymbol::Class, Visibility::Public, location);
}

void GenericClassDefSymbol::serializeTo(ASTSerializer& serializer) const {
    if (firstForward)
        serializer.write("forward", *firstForward);
}

GenericClassDefSymbol::SpecializationKey::SpecializationKey(
    const GenericClassDefSymbol& def, span<const ConstantValue* const> paramValues,
    span<const Type* const> typeParams) :
    definition(&def),
    paramValues(paramValues), typeParams(typeParams) {

    // Precompute the hash.
    size_t h = 0;
    hash_combine(h, definition);
    for (auto val : paramValues)
        hash_combine(h, val ? val->hash() : 0);
    for (auto type : typeParams)
        hash_combine(h, type ? type->hash() : 0);
    savedHash = h;
}

bool GenericClassDefSymbol::SpecializationKey::operator==(const SpecializationKey& other) const {
    if (savedHash != other.savedHash || definition != other.definition ||
        paramValues.size() != other.paramValues.size() ||
        typeParams.size() != other.typeParams.size()) {
        return false;
    }

    for (auto lit = paramValues.begin(), rit = other.paramValues.begin(); lit != paramValues.end();
         lit++, rit++) {
        const ConstantValue* l = *lit;
        const ConstantValue* r = *rit;
        if (l && r) {
            if (!(*l == *r))
                return false;
        }
        else {
            if (l != r)
                return false;
        }
    }

    for (auto lit = typeParams.begin(), rit = other.typeParams.begin(); lit != typeParams.end();
         lit++, rit++) {
        const Type* l = *lit;
        const Type* r = *rit;
        if (l && r) {
            if (!l->isMatching(*r))
                return false;
        }
        else {
            if (l != r)
                return false;
        }
    }

    return true;
}

} // namespace slang
