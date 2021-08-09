//------------------------------------------------------------------------------
// ClassSymbols.cpp
// Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/ClassSymbols.h"

#include "ParameterBuilder.h"

#include "slang/binding/AssignmentExpressions.h"
#include "slang/binding/CallExpression.h"
#include "slang/binding/Constraints.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/SymbolBuilders.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"

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
    RandMode randMode = RandMode::None;

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
                randMode = RandMode::Rand;
                break;
            case TokenKind::RandCKeyword:
                randMode = RandMode::RandC;
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
        var->randMode = randMode;
        var->setDeclaredType(*dataSyntax.type);
        var->setFromDeclarator(*declarator);
        var->setAttributes(scope, syntax.attributes);
        results.append(var);

        if (randMode != RandMode::None)
            var->getDeclaredType()->addFlags(DeclaredTypeFlags::Rand);

        if (isConst && lifetime == VariableLifetime::Static && !declarator->initializer)
            scope.addDiag(diag::StaticConstNoInitializer, declarator->name.range());
    }
}

void ClassPropertySymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("visibility", toString(visibility));
}

void ClassType::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void ClassType::checkForwardDecls() const {
    if (firstForward) {
        auto category = ForwardingTypedefSymbol::Class;
        if (isInterface)
            category = ForwardingTypedefSymbol::InterfaceClass;
        firstForward->checkType(category, Visibility::Public, location);
    }
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
    result->populate(scope, syntax);
    return *result;
}

void ClassType::populate(const Scope& scope, const ClassDeclarationSyntax& syntax) {
    // Save the current member index -- for generic classes, this is the location that
    // can see all parameter members but nothing else. This is needed to correctly
    // resolve type parameters used in extends and implements clauses.
    if (auto last = getLastMember())
        headerIndex = last->getIndex() + 1;
    else
        headerIndex = SymbolIndex(1);

    if (syntax.virtualOrInterface.kind == TokenKind::VirtualKeyword)
        isAbstract = true;
    else if (syntax.virtualOrInterface.kind == TokenKind::InterfaceKeyword)
        isInterface = true;

    setSyntax(syntax);
    for (auto member : syntax.items)
        addMembers(*member);

    // All class types get some built-in methods.
    auto& comp = getCompilation();
    auto& void_t = comp.getVoidType();
    auto& int_t = comp.getIntType();
    auto& string_t = comp.getStringType();

    auto checkOverride = [](auto& s) {
        return s.subroutineKind == SubroutineKind::Function && s.getArguments().empty() &&
               s.getReturnType().isVoid() && s.visibility == Visibility::Public &&
               s.flags == MethodFlags::None;
    };

    auto& scopeNameMap = getUnelaboratedNameMap();
    auto makeFunc = [&](string_view funcName, const Type& returnType, bool allowOverride,
                        bitmask<MethodFlags> extraFlags = MethodFlags::None,
                        SubroutineKind subroutineKind =
                            SubroutineKind::Function) -> optional<MethodBuilder> {
        if (auto it = scopeNameMap.find(funcName); it != scopeNameMap.end()) {
            auto existing = it->second;
            if (allowOverride) {
                bool ok = false;
                if (existing->kind == SymbolKind::Subroutine)
                    ok = checkOverride(existing->as<SubroutineSymbol>());
                else if (existing->kind == SymbolKind::MethodPrototype)
                    ok = checkOverride(existing->as<MethodPrototypeSymbol>());

                if (!ok)
                    scope.addDiag(diag::InvalidRandomizeOverride, existing->location) << funcName;
            }
            else {
                scope.addDiag(diag::InvalidMethodOverride, existing->location) << funcName;
            }
            return {};
        }

        MethodBuilder builder(comp, funcName, returnType, subroutineKind);
        builder.addFlags(extraFlags);
        addMember(builder.symbol);
        return builder;
    };

    makeFunc("randomize", int_t, false, MethodFlags::Virtual | MethodFlags::Randomize);
    makeFunc("pre_randomize", void_t, true);
    makeFunc("post_randomize", void_t, true);
    makeFunc("get_randstate", string_t, false);

    auto set_randstate = makeFunc("set_randstate", void_t, false);
    if (set_randstate)
        set_randstate->addArg("state", string_t);

    auto srandom = makeFunc("srandom", void_t, false);
    if (srandom)
        srandom->addArg("seed", int_t);

    auto rand_mode = makeFunc("rand_mode", void_t, false, MethodFlags::None, SubroutineKind::Task);
    if (rand_mode)
        rand_mode->addArg("on_ff", comp.getBitType());

    auto constraint_mode =
        makeFunc("constraint_mode", void_t, false, MethodFlags::None, SubroutineKind::Task);
    if (constraint_mode)
        constraint_mode->addArg("on_ff", comp.getBitType());

    // This needs to happen last, otherwise setting "needs elaboration" before
    // trying to access the name map can cause infinite recursion.
    if (syntax.extendsClause || syntax.implementsClause)
        setNeedElaboration();
}

void ClassType::inheritMembers(function_ref<void(const Symbol&)> insertCB) const {
    auto syntax = getSyntax();
    ASSERT(syntax);

    BindContext context(*this, LookupLocation(this, uint32_t(headerIndex)));

    auto& classSyntax = syntax->as<ClassDeclarationSyntax>();
    if (classSyntax.extendsClause)
        handleExtends(*classSyntax.extendsClause, context, insertCB);

    if (classSyntax.implementsClause)
        handleImplements(*classSyntax.implementsClause, context, insertCB);
}

void ClassType::handleExtends(const ExtendsClauseSyntax& extendsClause, const BindContext& context,
                              function_ref<void(const Symbol&)> insertCB) const {
    auto baseType = Lookup::findClass(*extendsClause.baseName, context);
    if (!baseType)
        return;

    // A normal class can't extend an interface class. This method won't be called
    // for an interface class, so we don't need to check that again here.
    if (baseType->isInterface) {
        context.addDiag(diag::ExtendIfaceFromClass, extendsClause.sourceRange()) << baseType->name;
        return;
    }

    // Assign this member before resolving anything below, because they
    // may try to check the base class of this type.
    baseClass = baseType;

    // Inherit all base class members that don't conflict with our declared symbols.
    const Symbol* baseConstructor = nullptr;
    auto& comp = context.getCompilation();
    auto& scopeNameMap = getNameMap();
    bool pureVirtualError = false;

    for (auto& member : baseType->members()) {
        if (member.name.empty())
            continue;

        // Don't inherit constructors.
        if (member.kind == SymbolKind::Subroutine &&
            (member.as<SubroutineSymbol>().flags & MethodFlags::Constructor) != 0) {
            baseConstructor = &member;
            continue;
        }
        if (member.kind == SymbolKind::MethodPrototype &&
            (member.as<MethodPrototypeSymbol>().flags & MethodFlags::Constructor) != 0) {
            baseConstructor = member.as<MethodPrototypeSymbol>().getSubroutine();
            continue;
        }

        // Don't inherit if the member is already overriden.
        if (auto it = scopeNameMap.find(member.name); it != scopeNameMap.end())
            continue;

        // If the symbol itself was already inherited, create a new wrapper around
        // it for our own scope.
        const Symbol* toWrap = &member;
        if (member.kind == SymbolKind::TransparentMember)
            toWrap = &member.as<TransparentMemberSymbol>().wrapped;

        // If this is a pure virtual method being inherited and we aren't ourselves
        // an abstract class, issue an error.
        if (!isAbstract && toWrap->kind == SymbolKind::MethodPrototype) {
            auto& sub = toWrap->as<MethodPrototypeSymbol>();
            if (sub.flags & MethodFlags::Pure) {
                if (!pureVirtualError) {
                    auto& diag =
                        context.addDiag(diag::InheritFromAbstract, extendsClause.sourceRange());
                    diag << name;
                    diag << baseType->name;
                    diag << sub.name;
                    diag.addNote(diag::NoteDeclarationHere, sub.location);
                    pureVirtualError = true;
                }
                continue;
            }
        }

        if (!isAbstract && toWrap->kind == SymbolKind::ConstraintBlock) {
            auto& cb = toWrap->as<ConstraintBlockSymbol>();
            if (cb.isPure) {
                if (!pureVirtualError) {
                    auto& diag = context.addDiag(diag::InheritFromAbstractConstraint,
                                                 extendsClause.sourceRange());
                    diag << name;
                    diag << baseType->name;
                    diag << cb.name;
                    diag.addNote(diag::NoteDeclarationHere, cb.location);
                    pureVirtualError = true;
                }
                continue;
            }
        }

        // All symbols get inserted into the beginning of the scope using the
        // provided insertion callback. We insert them as TransparentMemberSymbols
        // so that we can trace a path back to the actual location they are declared.
        auto wrapper = comp.emplace<TransparentMemberSymbol>(*toWrap);
        insertCB(*wrapper);
    }

    auto checkForOverride = [&](auto& member) {
        // Constructors and static methods can never be virtual.
        if (member.flags.has(MethodFlags::Constructor | MethodFlags::Static))
            return;

        // Look in the parent class for a method with the same name.
        auto currentBase = baseType;
        while (true) {
            const Symbol* found = currentBase->find(member.name);
            if (found) {
                if (found->kind == SymbolKind::Subroutine) {
                    auto& baseSub = found->as<SubroutineSymbol>();
                    if (baseSub.isVirtual())
                        member.setOverride(baseSub);
                }
                break;
            }

            // Otherwise it could be inherited from a higher-level base.
            auto possibleBase = currentBase->getBaseClass();
            if (!possibleBase)
                break;

            currentBase = &possibleBase->getCanonicalType().as<ClassType>();
        }
    };

    // Check all methods in our class for overriding virtual methods in parent classes.
    for (auto& member : members()) {
        if (member.kind == SymbolKind::Subroutine)
            checkForOverride(member.as<SubroutineSymbol>());
        else if (member.kind == SymbolKind::MethodPrototype) {
            auto& proto = member.as<MethodPrototypeSymbol>();
            checkForOverride(proto);

            if (auto baseSub = proto.getOverride()) {
                if (auto protoSub = proto.getSubroutine()) {
                    SubroutineSymbol::checkVirtualMethodMatch(
                        *context.scope, baseSub->as<SubroutineSymbol>(), *protoSub,
                        /* allowDerivedReturn */ true);
                }
            }
        }
        else if (member.kind == SymbolKind::ConstraintBlock) {
            // Constraint blocks can also be overriden -- check that 'static'ness
            // matches between base and derived if the base is pure.
            auto currentBase = baseType;
            while (true) {
                const Symbol* found = currentBase->find(member.name);
                if (found) {
                    if (found->kind == SymbolKind::ConstraintBlock) {
                        auto& baseConstraint = found->as<ConstraintBlockSymbol>();
                        if (baseConstraint.isPure &&
                            baseConstraint.isStatic !=
                                member.as<ConstraintBlockSymbol>().isStatic) {
                            auto& diag =
                                context.addDiag(diag::MismatchStaticConstraint, member.location);
                            diag.addNote(diag::NoteDeclarationHere, found->location);
                        }
                    }
                    break;
                }

                // Otherwise it could be inherited from a higher-level base.
                auto possibleBase = currentBase->getBaseClass();
                if (!possibleBase)
                    break;

                currentBase = &possibleBase->getCanonicalType().as<ClassType>();
            }
        }
    }

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

        // If the body is invalid, early out now so we don't report
        // spurious errors on top of it.
        auto& body = ourConstructor->as<SubroutineSymbol>().getBody();
        if (body.bad())
            return;

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

    if (auto extendsArgs = extendsClause.arguments) {
        // Can't have both a super.new and extends arguments.
        if (baseConstructorCall) {
            auto& diag =
                context.addDiag(diag::BaseConstructorDuplicate, baseConstructorCall->sourceRange);
            diag.addNote(diag::NotePreviousUsage, extendsArgs->getFirstToken().location());
            return;
        }

        // If we have a base class constructor, create the call to it.
        if (baseConstructor) {
            SourceRange range = extendsClause.sourceRange();
            Lookup::ensureVisible(*baseConstructor, context, range);

            baseConstructorCall =
                &CallExpression::fromArgs(comp, &baseConstructor->as<SubroutineSymbol>(), nullptr,
                                          extendsArgs, range, context);
        }
        else if (!extendsArgs->parameters.empty()) {
            auto& diag = context.addDiag(diag::TooManyArguments, extendsArgs->sourceRange());
            diag << baseClass->name;
            diag << 0;
            diag << extendsArgs->parameters.size();
        }
    }

    // If we have a base class constructor and nothing called it, make sure
    // it has no arguments or all of the arguments have default values.
    if (baseConstructor && !baseConstructorCall) {
        for (auto arg : baseConstructor->as<SubroutineSymbol>().getArguments()) {
            if (!arg->getInitializer()) {
                auto& diag =
                    context.addDiag(diag::BaseConstructorNotCalled, extendsClause.sourceRange());
                diag << name << baseClass->name;
                diag.addNote(diag::NoteDeclarationHere, baseConstructor->location);
                return;
            }
        }

        Lookup::ensureVisible(*baseConstructor, context, extendsClause.sourceRange());
    }
}

// Recursively finds interface classes that are implemented and adds them
// to the vector, if they haven't been added already.
static void findIfaces(const ClassType& type, SmallVector<const Type*>& ifaces,
                       SmallSet<const Symbol*, 4>& visited) {
    if (type.isInterface) {
        if (visited.emplace(&type).second)
            ifaces.append(&type);
    }

    for (auto iface : type.getImplementedInterfaces()) {
        if (visited.emplace(iface).second)
            ifaces.append(iface);
    }

    if (auto base = type.getBaseClass())
        findIfaces(base->getCanonicalType().as<ClassType>(), ifaces, visited);
}

void ClassType::handleImplements(const ImplementsClauseSyntax& implementsClause,
                                 const BindContext& context,
                                 function_ref<void(const Symbol&)> insertCB) const {
    auto& comp = context.getCompilation();
    SmallVectorSized<const Type*, 4> ifaces;
    SmallSet<const Symbol*, 4> seenIfaces;

    if (isInterface) {
        // For an interface class, the implements clause actually uses the "extends"
        // keyword and acts to inherit all of the members from the specified parent interfaces.
        for (auto nameSyntax : implementsClause.interfaces) {
            const auto iface = Lookup::findClass(*nameSyntax, context, diag::ExtendClassFromIface);
            if (!iface)
                continue;

            // Inherit all members that don't conflict with our declared symbols.
            auto& scopeNameMap = getNameMap();
            for (auto& member : iface->members()) {
                if (member.name.empty())
                    continue;

                const Symbol* toWrap = &member;
                if (member.kind == SymbolKind::TransparentMember)
                    toWrap = &member.as<TransparentMemberSymbol>().wrapped;

                if (auto it = scopeNameMap.find(member.name); it != scopeNameMap.end()) {
                    if (it->second->kind == SymbolKind::TransparentMember) {
                        // If the symbol we found was itself inherited we have a potential
                        // name conflict. Check whether the symbol came from a parent we already
                        // handled (a "diamond relationship"), and if not we error.
                        auto& existing = it->second->as<TransparentMemberSymbol>().wrapped;
                        const Symbol* origExisting = &existing;
                        const Symbol* origNew = toWrap;
                        if (origExisting->kind == SymbolKind::MethodPrototype &&
                            origNew->kind == SymbolKind::MethodPrototype) {
                            // This checks to see if the method prototype overrides (in the case of
                            // interfaces, this means exactly redeclaring) a parent method. We
                            // should check the original symbols in this case.
                            if (auto overrides =
                                    origExisting->as<MethodPrototypeSymbol>().getOverride()) {
                                origExisting = overrides;
                            }

                            if (auto overrides =
                                    origNew->as<MethodPrototypeSymbol>().getOverride()) {
                                origNew = overrides;
                            }
                        }

                        if (origExisting != origNew) {
                            auto parent = existing.getParentScope();
                            ASSERT(parent);

                            auto& diag =
                                context.addDiag(diag::IfaceNameConflict, nameSyntax->sourceRange());
                            diag << member.name << iface->name << parent->asSymbol().name;
                            diag.addNote(diag::NoteDeclarationHere, toWrap->location);
                            diag.addNote(diag::NoteDeclarationHere, existing.location);
                        }
                    }
                    else if (it->second->kind == SymbolKind::MethodPrototype &&
                             toWrap->kind == SymbolKind::MethodPrototype) {
                        // If this is a locally declared method check that it matches the method
                        // declared in the parent interface.
                        auto& parent = toWrap->as<MethodPrototypeSymbol>();
                        auto& derived = it->second->as<MethodPrototypeSymbol>();

                        auto parentSub = parent.getSubroutine();
                        auto derivedSub = derived.getSubroutine();
                        if (parentSub && derivedSub) {
                            SubroutineSymbol::checkVirtualMethodMatch(
                                *this, *parentSub, *derivedSub, /* allowDerivedReturn */ false);
                        }

                        if (auto overrides = parent.getOverride())
                            derived.setOverride(*overrides);
                        else
                            derived.setOverride(parent);
                    }
                    else if (toWrap->kind == SymbolKind::MethodPrototype) {
                        auto& diag = context.addDiag(diag::IfaceMethodHidden, it->second->location);
                        diag << it->second->name << iface->name;
                        diag.addNote(diag::NoteDeclarationHere, toWrap->location);
                    }
                    continue;
                }

                auto wrapper = comp.emplace<TransparentMemberSymbol>(*toWrap);
                insertCB(*wrapper);
            }

            findIfaces(*iface, ifaces, seenIfaces);
        }
    }
    else {
        for (auto nameSyntax : implementsClause.interfaces) {
            const auto iface = Lookup::findClass(*nameSyntax, context, diag::ImplementNonIface);
            if (!iface)
                continue;

            for (auto& member : iface->members()) {
                if (member.name.empty())
                    continue;

                const Symbol* unwrapped = &member;
                if (member.kind == SymbolKind::TransparentMember)
                    unwrapped = &member.as<TransparentMemberSymbol>().wrapped;

                if (unwrapped->kind != SymbolKind::MethodPrototype)
                    continue;

                // For each method declared in an interface, look for a corresponding
                // implementation via a virtual method in the class.
                auto& method = unwrapped->as<MethodPrototypeSymbol>();
                auto methodSub = method.getSubroutine();
                if (!methodSub)
                    continue;

                auto impl = find(method.name);
                if (!impl || impl->kind != SymbolKind::Subroutine) {
                    auto& diag =
                        context.addDiag(diag::IfaceMethodNoImpl, nameSyntax->sourceRange());
                    diag << name << method.name << iface->name;
                    continue;
                }

                // The method must be virtual in order to be a valid implementation.
                auto& implSub = impl->as<SubroutineSymbol>();
                if (!implSub.isVirtual()) {
                    auto& diag =
                        context.addDiag(diag::IfaceMethodNotVirtual, nameSyntax->sourceRange());
                    diag << name << method.name << iface->name;
                    diag.addNote(diag::NoteDeclarationHere, impl->location);
                    continue;
                }

                // Finally, verify the method signatures match.
                SubroutineSymbol::checkVirtualMethodMatch(*this, *methodSub, implSub,
                                                          /* allowDerivedReturn */ false);
            }

            findIfaces(*iface, ifaces, seenIfaces);
        }
    }

    implementsIfaces = ifaces.copy(comp);
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

    if (syntax.virtualOrInterface.kind == TokenKind::InterfaceKeyword)
        result->isInterface = true;

    // Extract information about parameters and save it for later use
    // when building specializations.
    ASSERT(syntax.parameters);
    ParameterBuilder::createDecls(scope, *syntax.parameters, result->paramDecls);

    return *result;
}

const Type* GenericClassDefSymbol::getDefaultSpecialization() const {
    if (defaultSpecialization)
        return *defaultSpecialization;

    auto scope = getParentScope();
    ASSERT(scope);

    auto result = getSpecializationImpl(BindContext(*scope, LookupLocation::max), location,
                                        /* forceInvalidParams */ false, nullptr);
    defaultSpecialization = result;
    return result;
}

const Type& GenericClassDefSymbol::getSpecialization(
    const BindContext& context, const ParameterValueAssignmentSyntax& syntax) const {

    auto result = getSpecializationImpl(context, syntax.getFirstToken().location(),
                                        /* forceInvalidParams */ false, &syntax);
    if (!result)
        return context.getCompilation().getErrorType();

    return *result;
}

const Type& GenericClassDefSymbol::getInvalidSpecialization() const {
    auto scope = getParentScope();
    ASSERT(scope);

    auto result = getSpecializationImpl(BindContext(*scope, LookupLocation::max), location,
                                        /* forceInvalidParams */ true, nullptr);
    if (!result)
        return scope->getCompilation().getErrorType();

    return *result;
}

const Type* GenericClassDefSymbol::getSpecializationImpl(
    const BindContext& context, SourceLocation instanceLoc, bool forceInvalidParams,
    const ParameterValueAssignmentSyntax* syntax) const {

    auto& comp = context.getCompilation();
    auto scope = getParentScope();
    ASSERT(scope);

    // Create a class type instance to hold the parameters. If it turns out we already
    // have this specialization cached we'll throw it away, but that's not a big deal.
    auto classType = comp.emplace<ClassType>(comp, name, location);
    classType->genericClass = this;
    classType->setParent(*scope, getIndex());

    ParameterBuilder paramBuilder(*context.scope, name, paramDecls);
    if (syntax)
        paramBuilder.setAssignments(*syntax);

    // If this is for the default specialization, `syntax` will be null.
    // We want to suppress errors about params not having values and just
    // return null so that the caller can figure out if this is actually a problem.
    bool isForDefault = syntax == nullptr;
    if (!paramBuilder.createParams(*classType, context.getLocation(), instanceLoc,
                                   forceInvalidParams, isForDefault)) {
        if (isForDefault)
            return nullptr;

        // Otherwise use an error type instead.
        return &comp.getErrorType();
    }

    SpecializationKey key(*this, paramBuilder.paramValues.copy(comp),
                          paramBuilder.typeParams.copy(comp));
    if (auto it = specMap.find(key); it != specMap.end())
        return it->second;

    // Not found, so this is a new entry. Fill in its members and store the
    // specialization for later lookup. If we have a specialization function,
    // call that instead of trying to create from our syntax node.
    if (specializeFunc)
        specializeFunc(comp, *classType);
    else
        classType->populate(*scope, getSyntax()->as<ClassDeclarationSyntax>());
    specMap.emplace(key, classType);
    return classType;
}

void GenericClassDefSymbol::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void GenericClassDefSymbol::checkForwardDecls() const {
    if (firstForward) {
        auto category = ForwardingTypedefSymbol::Class;
        if (isInterface)
            category = ForwardingTypedefSymbol::InterfaceClass;
        firstForward->checkType(category, Visibility::Public, location);
    }
}

void GenericClassDefSymbol::addParameterDecl(const Definition::ParameterDecl& decl) {
    paramDecls.append(decl);
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

ConstraintBlockSymbol::ConstraintBlockSymbol(Compilation& c, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::ConstraintBlock, name, loc), Scope(c, this) {
}

ConstraintBlockSymbol* ConstraintBlockSymbol::fromSyntax(
    const Scope& scope, const ConstraintDeclarationSyntax& syntax) {

    auto& comp = scope.getCompilation();
    if (syntax.name->kind == SyntaxKind::ScopedName) {
        // Remember the location in the parent scope where we *would* have inserted this
        // constraint, for later use during lookup.
        uint32_t index = 1;
        if (auto last = scope.getLastMember())
            index = (uint32_t)last->getIndex() + 1;

        comp.addOutOfBlockDecl(scope, syntax.name->as<ScopedNameSyntax>(), syntax,
                               SymbolIndex(index));
        return nullptr;
    }

    auto nameToken = syntax.name->getLastToken();
    auto result =
        comp.emplace<ConstraintBlockSymbol>(comp, nameToken.valueText(), nameToken.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    // Static is the only allowed qualifier.
    for (auto qual : syntax.qualifiers) {
        if (qual.kind == TokenKind::StaticKeyword)
            result->isStatic = true;
        else if (qual.kind == TokenKind::PureKeyword || qual.kind == TokenKind::ExternKeyword) {
            // This is an error, pure and extern declarations can't declare bodies.
            scope.addDiag(diag::UnexpectedConstraintBlock, syntax.block->sourceRange())
                << qual.range();
            break;
        }
    }

    if (!result->isStatic)
        result->addThisVar(scope.asSymbol().as<ClassType>());

    return result;
}

ConstraintBlockSymbol& ConstraintBlockSymbol::fromSyntax(const Scope& scope,
                                                         const ConstraintPrototypeSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto nameToken = syntax.name->getLastToken();
    auto result =
        comp.emplace<ConstraintBlockSymbol>(comp, nameToken.valueText(), nameToken.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    result->isExtern = true;

    for (auto qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::StaticKeyword:
                result->isStatic = true;
                break;
            case TokenKind::ExternKeyword:
                result->isExplicitExtern = true;
                break;
            case TokenKind::PureKeyword:
                result->isPure = true;
                break;
            default:
                break;
        }
    }

    if (result->isPure && scope.asSymbol().kind == SymbolKind::ClassType) {
        auto& classType = scope.asSymbol().as<ClassType>();
        if (!classType.isAbstract)
            scope.addDiag(diag::PureConstraintInAbstract, nameToken.range());
    }

    if (!result->isStatic)
        result->addThisVar(scope.asSymbol().as<ClassType>());

    return *result;
}

const Constraint& ConstraintBlockSymbol::getConstraints() const {
    if (constraint)
        return *constraint;

    auto syntax = getSyntax();
    auto scope = getParentScope();
    ASSERT(syntax && scope);
    BindContext context(*this, LookupLocation::max);

    if (syntax->kind == SyntaxKind::ConstraintPrototype) {
        // The out-of-block definition must be in our parent scope.
        auto& parentSym = scope->asSymbol();
        auto& outerScope = *parentSym.getParentScope();
        auto& comp = outerScope.getCompilation();

        auto [declSyntax, index, used] = comp.findOutOfBlockDecl(outerScope, parentSym.name, name);
        if (!declSyntax || declSyntax->kind != SyntaxKind::ConstraintDeclaration) {
            if (!isPure) {
                DiagCode code = isExplicitExtern ? diag::NoMemberImplFound : diag::NoConstraintBody;
                outerScope.addDiag(code, location) << name;
            }
            constraint = scope->getCompilation().emplace<InvalidConstraint>(nullptr);
            return *constraint;
        }

        auto& cds = declSyntax->as<ConstraintDeclarationSyntax>();
        *used = true;

        if (isPure) {
            auto& diag = outerScope.addDiag(diag::BodyForPureConstraint, cds.name->sourceRange());
            diag.addNote(diag::NoteDeclarationHere, location);
            constraint = scope->getCompilation().emplace<InvalidConstraint>(nullptr);
            return *constraint;
        }

        // The method definition must be located after the class definition.
        outOfBlockIndex = index;
        if (index <= parentSym.getIndex()) {
            auto& diag = outerScope.addDiag(diag::MemberDefinitionBeforeClass,
                                            cds.name->getLastToken().location());
            diag << name << parentSym.name;
            diag.addNote(diag::NoteDeclarationHere, parentSym.location);
        }

        bool declStatic = false;
        for (auto qual : cds.qualifiers) {
            if (qual.kind == TokenKind::StaticKeyword) {
                declStatic = true;
                break;
            }
        }

        if (declStatic != isStatic) {
            auto& diag =
                outerScope.addDiag(diag::MismatchStaticConstraint, cds.getFirstToken().location());
            diag.addNote(diag::NoteDeclarationHere, location);
        }

        constraint = &Constraint::bind(*cds.block, context);
        return *constraint;
    }

    constraint = &Constraint::bind(*syntax->as<ConstraintDeclarationSyntax>().block, context);
    return *constraint;
}

void ConstraintBlockSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("constraints", getConstraints());
    serializer.write("isStatic", isStatic);
    serializer.write("isExtern", isExtern);
    serializer.write("isExplicitExtern", isExplicitExtern);
}

void ConstraintBlockSymbol::addThisVar(const Type& type) {
    auto tv = getCompilation().emplace<VariableSymbol>("this", type.location,
                                                       VariableLifetime::Automatic);
    tv->setType(type);
    tv->isConstant = true;
    tv->isCompilerGenerated = true;
    thisVar = tv;
    addMember(*thisVar);
}

} // namespace slang
