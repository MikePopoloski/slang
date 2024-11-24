//------------------------------------------------------------------------------
// ClassSymbols.cpp
// Class-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/ClassSymbols.h"

#include "ParameterBuilder.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Constraints.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/statements/MiscStatements.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/SymbolBuilders.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

ClassPropertySymbol::ClassPropertySymbol(std::string_view name, SourceLocation loc,
                                         VariableLifetime lifetime, Visibility visibility) :
    VariableSymbol(SymbolKind::ClassProperty, name, loc, lifetime), visibility(visibility) {
}

void ClassPropertySymbol::fromSyntax(const Scope& scope,
                                     const ClassPropertyDeclarationSyntax& syntax,
                                     SmallVectorBase<const ClassPropertySymbol*>& results) {
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
                SLANG_UNREACHABLE;
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
                SLANG_UNREACHABLE;
        }
    }

    for (auto declarator : dataSyntax.declarators) {
        auto var = comp.emplace<ClassPropertySymbol>(declarator->name.valueText(),
                                                     declarator->name.location(), lifetime,
                                                     visibility);
        var->randMode = randMode;
        var->setDeclaredType(*dataSyntax.type);
        var->setFromDeclarator(*declarator);
        var->setAttributes(scope, syntax.attributes);
        results.push_back(var);

        if (isConst)
            var->flags |= VariableFlags::Const;

        if (randMode != RandMode::None)
            var->getDeclaredType()->addFlags(DeclaredTypeFlags::Rand);

        if (isConst && lifetime == VariableLifetime::Static && !declarator->initializer)
            scope.addDiag(diag::StaticConstNoInitializer, declarator->name.range());
    }
}

void ClassPropertySymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("visibility", toString(visibility));
    if (randMode != RandMode::None)
        serializer.write("randMode", toString(randMode));
}

void ClassType::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void ClassType::checkForwardDecls() const {
    if (firstForward) {
        auto typeRestriction = ForwardTypeRestriction::Class;
        if (isInterface)
            typeRestriction = ForwardTypeRestriction::InterfaceClass;
        firstForward->checkType(typeRestriction, Visibility::Public, location);
    }
}

ClassType::ClassType(Compilation& compilation, std::string_view name, SourceLocation loc) :
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

    if (syntax.finalSpecifier && syntax.finalSpecifier->keyword.kind == TokenKind::FinalKeyword)
        isFinal = true;

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
    auto makeFunc = [&](std::string_view funcName, const Type& returnType, bool allowOverride,
                        bitmask<MethodFlags> extraFlags = MethodFlags::None,
                        SubroutineKind subroutineKind =
                            SubroutineKind::Function) -> std::optional<MethodBuilder> {
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

    auto rand_mode = makeFunc("rand_mode", void_t, false, MethodFlags::None,
                              SubroutineKind::Function);
    if (rand_mode)
        rand_mode->addArg("on_ff", comp.getBitType());

    auto constraint_mode = makeFunc("constraint_mode", void_t, false, MethodFlags::None,
                                    SubroutineKind::Function);
    if (constraint_mode)
        constraint_mode->addArg("on_ff", comp.getBitType());

    // Give this class a "thisVar" that can be used by non-static class
    // property initializers to refer to their own instance.
    auto tv = comp.emplace<VariableSymbol>("this", location, VariableLifetime::Automatic);
    tv->setType(*this);
    tv->flags |= VariableFlags::Const | VariableFlags::CompilerGenerated;
    tv->setParent(*this);
    thisVar = tv;

    // This needs to happen last, otherwise setting "needs elaboration" before
    // trying to access the name map can cause infinite recursion.
    if (syntax.extendsClause || syntax.implementsClause)
        setNeedElaboration();
}

void ClassType::inheritMembers(function_ref<void(const Symbol&)> insertCB) const {
    auto syntax = getSyntax();
    SLANG_ASSERT(syntax);

    ASTContext context(*this, LookupLocation(this, uint32_t(headerIndex)));

    auto& classSyntax = syntax->as<ClassDeclarationSyntax>();
    if (classSyntax.extendsClause)
        handleExtends(*classSyntax.extendsClause, context, insertCB);

    if (classSyntax.implementsClause)
        handleImplements(*classSyntax.implementsClause, context, insertCB);
}

void ClassType::handleExtends(const ExtendsClauseSyntax& extendsClause, const ASTContext& context,
                              function_ref<void(const Symbol&)> insertCB) const {
    auto& comp = context.getCompilation();
    auto baseType = Lookup::findClass(*extendsClause.baseName, context);
    if (!baseType) {
        baseClass = &comp.getErrorType();
        return;
    }

    // A normal class can't extend an interface class. This method won't be called
    // for an interface class, so we don't need to check that again here.
    if (baseType->isInterface) {
        baseClass = &comp.getErrorType();
        context.addDiag(diag::ExtendIfaceFromClass, extendsClause.sourceRange()) << baseType->name;
        return;
    }

    if (baseType->isFinal) {
        baseClass = &comp.getErrorType();
        context.addDiag(diag::ExtendFromFinal, extendsClause.sourceRange()) << baseType->name;
        return;
    }

    // Make sure there are no cycles in the inheritance chain.
    auto currBase = baseType;
    while (true) {
        if (currBase == this) {
            context.addDiag(diag::ClassInheritanceCycle, extendsClause.sourceRange()) << name;
            baseClass = &comp.getErrorType();
            return;
        }

        auto next = currBase->getBaseClass();
        if (!next || next->isError())
            break;

        currBase = &next->getCanonicalType().as<ClassType>();
    }

    // Assign this member before resolving anything below, because they
    // may try to check the base class of this type.
    baseClass = baseType;

    // Inherit all base class members that don't conflict with our declared symbols.
    auto& scopeNameMap = getNameMap();
    bool pureVirtualError = false;

    for (auto& member : baseType->members()) {
        if (member.name.empty())
            continue;

        // Don't inherit constructors.
        if (member.kind == SymbolKind::Subroutine &&
            member.as<SubroutineSymbol>().flags.has(MethodFlags::Constructor)) {
            baseConstructor = &member;
            continue;
        }
        if (member.kind == SymbolKind::MethodPrototype &&
            member.as<MethodPrototypeSymbol>().flags.has(MethodFlags::Constructor)) {
            baseConstructor = member.as<MethodPrototypeSymbol>().getSubroutine();
            continue;
        }

        // Don't inherit if the member is already overridden.
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
            if (sub.flags.has(MethodFlags::Pure)) {
                if (!pureVirtualError) {
                    auto& diag = context.addDiag(diag::InheritFromAbstract,
                                                 extendsClause.sourceRange());
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
            if (cb.flags.has(ConstraintBlockFlags::Pure)) {
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

    auto checkOverrideSpecifiers = [&](auto& base, auto& derived) {
        if (derived.flags.has(MethodFlags::Initial) && base.isVirtual()) {
            auto& diag = context.addDiag(diag::OverridingInitial, derived.location);
            diag << derived.name;
            diag.addNote(diag::NoteDeclarationHere, base.location);
        }
        else if (base.flags.has(MethodFlags::Final)) {
            auto& diag = context.addDiag(diag::OverridingFinal, derived.location);
            diag << derived.name;
            diag.addNote(diag::NoteDeclarationHere, base.location);
        }
        else if (!base.isVirtual() && derived.flags.has(MethodFlags::Extends)) {
            context.addDiag(diag::OverridingExtends, derived.location) << derived.name;
        }
    };

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
                    checkOverrideSpecifiers(baseSub, member);
                    if (baseSub.isVirtual())
                        member.setOverride(baseSub);
                    return;
                }
                break;
            }

            // Otherwise it could be inherited from a higher-level base.
            auto possibleBase = currentBase->getBaseClass();
            if (!possibleBase)
                break;

            if (possibleBase->isError())
                return;

            currentBase = &possibleBase->getCanonicalType().as<ClassType>();
        }

        // No base method found; if our member is marked 'extends' it's an error.
        if (member.flags.has(MethodFlags::Extends))
            context.addDiag(diag::OverridingExtends, member.location) << member.name;
    };

    // Check all methods in our class for overriding virtual methods in parent classes.
    for (auto& member : members()) {
        if (member.kind == SymbolKind::Subroutine) {
            checkForOverride(member.as<SubroutineSymbol>());
        }
        else if (member.kind == SymbolKind::MethodPrototype) {
            auto& proto = member.as<MethodPrototypeSymbol>();
            checkForOverride(proto);

            if (auto baseSub = proto.getOverride()) {
                if (auto protoSub = proto.getSubroutine()) {
                    SubroutineSymbol::checkVirtualMethodMatch(*context.scope,
                                                              baseSub->as<SubroutineSymbol>(),
                                                              *protoSub,
                                                              /* allowDerivedReturn */ true);
                }
            }
        }
        else if (member.kind == SymbolKind::ConstraintBlock) {
            // Constraint blocks can also be overridden -- check that 'static'ness
            // matches between base and derived if the base is pure.
            bool isOverridden = false;
            auto currentBase = baseType;
            auto& derived = member.as<ConstraintBlockSymbol>();
            while (true) {
                const Symbol* found = currentBase->find(member.name);
                if (found) {
                    if (found->kind == SymbolKind::ConstraintBlock) {
                        isOverridden = true;
                        auto& baseConstraint = found->as<ConstraintBlockSymbol>();
                        if (baseConstraint.flags.has(ConstraintBlockFlags::Pure) &&
                            baseConstraint.flags.has(ConstraintBlockFlags::Static) !=
                                member.as<ConstraintBlockSymbol>().flags.has(
                                    ConstraintBlockFlags::Static)) {
                            auto& diag = context.addDiag(diag::MismatchStaticConstraint,
                                                         member.location);
                            diag.addNote(diag::NoteDeclarationHere, found->location);
                        }

                        if (derived.flags.has(ConstraintBlockFlags::Initial)) {
                            auto& diag = context.addDiag(diag::OverridingInitial, derived.location);
                            diag << derived.name;
                            diag.addNote(diag::NoteDeclarationHere, baseConstraint.location);
                        }
                        else if (baseConstraint.flags.has(ConstraintBlockFlags::Final)) {
                            auto& diag = context.addDiag(diag::OverridingFinal, derived.location);
                            diag << derived.name;
                            diag.addNote(diag::NoteDeclarationHere, baseConstraint.location);
                        }
                    }
                    break;
                }

                // Otherwise it could be inherited from a higher-level base.
                auto possibleBase = currentBase->getBaseClass();
                if (!possibleBase || possibleBase->isError())
                    break;

                currentBase = &possibleBase->getCanonicalType().as<ClassType>();
            }

            if (!isOverridden && derived.flags.has(ConstraintBlockFlags::Extends))
                context.addDiag(diag::OverridingExtends, member.location) << member.name;
        }
    }
}

const Expression* ClassType::getBaseConstructorCall() const {
    if (baseConstructorCall)
        return *baseConstructorCall;

    baseConstructorCall = nullptr;
    const Expression* callExpr = nullptr;

    auto syntax = getSyntax();
    SLANG_ASSERT(syntax);

    auto& classSyntax = syntax->as<ClassDeclarationSyntax>();
    if (!classSyntax.extendsClause)
        return nullptr;

    ensureElaborated();

    SLANG_ASSERT(baseClass);
    if (baseClass->isError())
        return nullptr;

    // If we have a constructor, find whether it invokes super.new in its body.
    bool constructorHasDefault = false;
    auto ourConstructor = getConstructor();
    if (ourConstructor) {
        auto checkForSuperNew = [&](const Statement& stmt) {
            if (stmt.kind == StatementKind::ExpressionStatement) {
                auto& expr = stmt.as<ExpressionStatement>().expr;
                if (expr.kind == ExpressionKind::NewClass &&
                    expr.as<NewClassExpression>().isSuperClass) {
                    callExpr = &expr;
                }
            }
        };

        // If the body is invalid, early out now so we don't report
        // spurious errors on top of it.
        constructorHasDefault = ourConstructor->flags.has(MethodFlags::DefaultedSuperArg);
        auto& body = ourConstructor->getBody();
        if (body.bad())
            return nullptr;

        if (body.kind != StatementKind::List) {
            checkForSuperNew(body);
        }
        else {
            for (auto stmt : body.as<StatementList>().list) {
                if (stmt->kind != StatementKind::VariableDeclaration) {
                    checkForSuperNew(*stmt);
                    break;
                }
            }
        }
    }

    ASTContext context(*this, LookupLocation(this, uint32_t(headerIndex)));
    auto& extendsClause = *classSyntax.extendsClause;

    // Can't have both a super.new and extends arguments.
    if (callExpr && (extendsClause.arguments || extendsClause.defaultedArg)) {
        auto argSyntax = extendsClause.arguments ? (const SyntaxNode*)extendsClause.arguments
                                                 : extendsClause.defaultedArg;
        auto& diag = context.addDiag(diag::BaseConstructorDuplicate, callExpr->sourceRange);
        diag.addNote(diag::NotePreviousUsage, argSyntax->getFirstToken().location());
        return nullptr;
    }

    if (auto extendsArgs = extendsClause.arguments) {
        // If we have a base class constructor, create the call to it.
        if (baseConstructor) {
            SourceRange range = extendsClause.sourceRange();
            Lookup::ensureVisible(*baseConstructor, context, range);

            callExpr = &CallExpression::fromArgs(context.getCompilation(),
                                                 &baseConstructor->as<SubroutineSymbol>(), nullptr,
                                                 extendsArgs, range, context);
        }
        else if (!extendsArgs->parameters.empty()) {
            auto& diag = context.addDiag(diag::TooManyArguments, extendsArgs->sourceRange());
            diag << baseClass->name;
            diag << 0;
            diag << extendsArgs->parameters.size();
        }
    }
    else if (extendsClause.defaultedArg) {
        SLANG_ASSERT(ourConstructor);
        if (!constructorHasDefault) {
            auto& diag = context.addDiag(diag::InvalidExtendsDefault, ourConstructor->location);
            diag.addNote(diag::NotePreviousUsage, extendsClause.defaultedArg->sourceRange());
        }

        constructorHasDefault = true;
    }

    // If we have a base class constructor and nothing called it, make sure
    // it has no arguments or all of the arguments have default values.
    // If our own constructor declares a 'default' arg then this requirement
    // is removed since we will insert the appropriate call arguments automatically.
    if (baseConstructor && !callExpr && !constructorHasDefault) {
        for (auto arg : baseConstructor->as<SubroutineSymbol>().getArguments()) {
            if (!arg->getDefaultValue()) {
                auto& diag = context.addDiag(diag::BaseConstructorNotCalled,
                                             extendsClause.sourceRange());
                diag << name << baseClass->name;
                diag.addNote(diag::NoteDeclarationHere, baseConstructor->location);
                return nullptr;
            }
        }

        Lookup::ensureVisible(*baseConstructor, context, extendsClause.sourceRange());
    }

    baseConstructorCall = callExpr;
    return callExpr;
}

const SubroutineSymbol* ClassType::getConstructor() const {
    if (auto constructor = find("new");
        constructor && constructor->kind == SymbolKind::Subroutine) {
        auto& sub = constructor->as<SubroutineSymbol>();
        if (sub.flags.has(MethodFlags::Constructor))
            return &sub;
    }

    // If our extends clause specifies 'default' for the argument list
    // we will auto-generate an appropriate constructor if the user
    // has not provided one.
    auto syntax = getSyntax();
    auto scope = getParentScope();
    if (syntax && scope) {
        auto extendsClause = syntax->as<ClassDeclarationSyntax>().extendsClause;
        if (extendsClause && extendsClause->defaultedArg) {
            auto& comp = scope->getCompilation();
            MethodBuilder builder(comp, "new", comp.getVoidType(), SubroutineKind::Function);
            builder.addFlags(MethodFlags::Constructor | MethodFlags::DefaultedSuperArg);

            SubroutineSymbol::inheritDefaultedArgList(builder.symbol, *this,
                                                      *extendsClause->defaultedArg, builder.args);

            insertMember(&builder.symbol, getLastMember(), true, true);
            return &builder.symbol;
        }
    }

    return nullptr;
}

// Recursively finds interface classes that are implemented and adds them
// to the vector, if they haven't been added already.
static void findIfaces(const ClassType& type, SmallVectorBase<const Type*>& ifaces,
                       SmallSet<const Symbol*, 4>& visited) {
    if (type.isInterface) {
        if (visited.emplace(&type).second)
            ifaces.push_back(&type);
    }

    for (auto iface : type.getImplementedInterfaces()) {
        if (visited.emplace(iface).second)
            ifaces.push_back(iface);
    }

    if (auto base = type.getBaseClass(); base && !base->isError())
        findIfaces(base->getCanonicalType().as<ClassType>(), ifaces, visited);
}

void ClassType::handleImplements(const ImplementsClauseSyntax& implementsClause,
                                 const ASTContext& context,
                                 function_ref<void(const Symbol&)> insertCB) const {
    auto& comp = context.getCompilation();
    SmallVector<const Type*> declaredIfacesBuf;
    SmallVector<const Type*> implementsIfacesBuf;
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
                            SLANG_ASSERT(parent);

                            auto& diag = context.addDiag(diag::IfaceNameConflict,
                                                         nameSyntax->sourceRange());
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

            declaredIfacesBuf.push_back(iface);
            findIfaces(*iface, implementsIfacesBuf, seenIfaces);
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
                    if (!baseClass || !baseClass->isError()) {
                        auto& diag = context.addDiag(diag::IfaceMethodNoImpl,
                                                     nameSyntax->sourceRange());
                        diag << name << method.name << iface->name;
                    }
                    continue;
                }

                // The method must be virtual in order to be a valid implementation.
                auto& implSub = impl->as<SubroutineSymbol>();
                if (!implSub.isVirtual()) {
                    auto& diag = context.addDiag(diag::IfaceMethodNotVirtual,
                                                 nameSyntax->sourceRange());
                    diag << name << method.name << iface->name;
                    diag.addNote(diag::NoteDeclarationHere, impl->location);
                    continue;
                }

                // Finally, verify the method signatures match.
                SubroutineSymbol::checkVirtualMethodMatch(*this, *methodSub, implSub,
                                                          /* allowDerivedReturn */ false);
            }

            declaredIfacesBuf.push_back(iface);
            findIfaces(*iface, implementsIfacesBuf, seenIfaces);
        }
    }

    declaredIfaces = declaredIfacesBuf.copy(comp);
    implementsIfaces = implementsIfacesBuf.copy(comp);
}

void ClassType::computeSize() const {
    ensureElaborated();
    cachedBitstreamWidth = 0;
    if (isInterface)
        return;

    ASTContext context(*this, LookupLocation(this, uint32_t(headerIndex)));

    // Note: no worry of class cycles here because we set cachedBitstreamWidth
    // to zero up above, which will avoid re-entering this function.
    uint64_t totalWidth = 0;
    bool hasDynamic = false;
    for (auto& prop : membersOfType<ClassPropertySymbol>()) {
        uint64_t width = prop.getType().getBitstreamWidth();
        if (width == 0)
            hasDynamic = true;

        totalWidth += width;
        if (totalWidth > MaxBitWidth) {
            context.addDiag(diag::ObjectTooLarge, location);
            return;
        }
    }

    if (!hasDynamic)
        cachedBitstreamWidth = totalWidth;
}

void ClassType::computeCycles() const {
    // Start out by setting hasCycles to true, so that if we call into
    // hasCycles() in a re-entrant fashion we'll see this result right away.
    ensureElaborated();
    cachedHasCycles = true;

    for (auto& prop : membersOfType<ClassPropertySymbol>()) {
        auto& propType = prop.getType().getCanonicalType();
        if (propType.isClass() && propType.as<ClassType>().hasCycles())
            return;
    }

    cachedHasCycles = false;
}

void ClassType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("isAbstract", isAbstract);
    serializer.write("isInterface", isInterface);
    serializer.write("isFinal", isFinal);
    if (firstForward)
        serializer.write("forward", *firstForward);
    if (genericClass)
        serializer.writeLink("genericClass", *genericClass);
    if (auto base = getBaseClass())
        serializer.write("baseClass", *base);
    if (auto expr = getBaseConstructorCall())
        serializer.write("baseConstructorCall", *expr);

    serializer.startArray("implements");
    for (auto type : getDeclaredInterfaces())
        serializer.serialize(*type);
    serializer.endArray();
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
    SLANG_ASSERT(syntax.parameters);
    ParameterBuilder::createDecls(scope, *syntax.parameters, result->paramDecls);

    return *result;
}

const Type* GenericClassDefSymbol::getDefaultSpecialization() const {
    if (defaultSpecialization)
        return *defaultSpecialization;

    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto result = getSpecializationImpl(ASTContext(*scope, LookupLocation::max), location,
                                        /* forceInvalidParams */ false, nullptr);
    defaultSpecialization = result;
    return result;
}

const Type& GenericClassDefSymbol::getSpecialization(
    const ASTContext& context, const ParameterValueAssignmentSyntax& syntax) const {

    auto result = getSpecializationImpl(context, syntax.getFirstToken().location(),
                                        /* forceInvalidParams */ false, &syntax);
    if (!result)
        return context.getCompilation().getErrorType();

    return *result;
}

const Type& GenericClassDefSymbol::getInvalidSpecialization() const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto result = getSpecializationImpl(ASTContext(*scope, LookupLocation::max), location,
                                        /* forceInvalidParams */ true, nullptr);
    if (!result)
        return scope->getCompilation().getErrorType();

    return *result;
}

const Type* GenericClassDefSymbol::getSpecializationImpl(
    const ASTContext& context, SourceLocation instanceLoc, bool forceInvalidParams,
    const ParameterValueAssignmentSyntax* syntax) const {

    auto& comp = context.getCompilation();
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto guard = ScopeGuard([this] { recursionDepth--; });
    if (++recursionDepth > comp.getOptions().maxRecursiveClassSpecialization) {
        context.addDiag(diag::RecursiveClassSpecialization, instanceLoc) << name;
        return &comp.getErrorType();
    }

    // Create a class type instance to hold the parameters. If it turns out we already
    // have this specialization cached we'll throw it away, but that's not a big deal.
    auto classType = comp.emplace<ClassType>(comp, name, location);
    classType->genericClass = this;
    classType->setParent(*scope, getIndex());

    // If this is for the default specialization, `syntax` will be null.
    // We want to suppress errors about params not having values and just
    // return null so that the caller can figure out if this is actually a problem.
    bool isForDefault = syntax == nullptr;

    ParameterBuilder paramBuilder(*context.scope, name, paramDecls);
    paramBuilder.setForceInvalidValues(forceInvalidParams);
    paramBuilder.setSuppressErrors(isForDefault);
    paramBuilder.setInstanceContext(context);
    if (syntax)
        paramBuilder.setAssignments(*syntax, /* isFromConfig */ false);

    SourceRange instRange = {instanceLoc, instanceLoc + 1};

    SmallVector<const ConstantValue*> paramValues;
    SmallVector<const Type*> typeParams;
    for (auto& decl : paramDecls) {
        auto& param = paramBuilder.createParam(decl, *classType, instanceLoc);
        if (paramBuilder.hasErrors()) {
            if (isForDefault)
                return nullptr;

            // Otherwise use an error type instead.
            return &comp.getErrorType();
        }

        if (!param.isLocalParam()) {
            auto& sym = param.symbol;
            if (sym.kind == SymbolKind::Parameter) {
                auto& ps = sym.as<ParameterSymbol>();
                paramValues.push_back(&ps.getValue(instRange));
            }
            else {
                auto& tps = sym.as<TypeParameterSymbol>();
                typeParams.push_back(&tps.targetType.getType());
            }
        }
    }

    detail::ClassSpecializationKey key(*this, paramValues.copy(comp), typeParams.copy(comp));
    if (auto it = specMap.find(key); it != specMap.end())
        return it->second;
    if (auto it = uninstantiatedSpecMap.find(key); it != uninstantiatedSpecMap.end())
        return it->second;

    // Not found, so this is a new entry. Fill in its members and store the
    // specialization for later lookup. If we have a specialization function,
    // call that instead of trying to create from our syntax node.
    if (specializeFunc)
        specializeFunc(comp, *classType, instanceLoc);
    else
        classType->populate(*scope, getSyntax()->as<ClassDeclarationSyntax>());

    if (!forceInvalidParams) {
        // If we're in an uninstantiated scope we save this specialization
        // in a separate map so that we don't try to elaborate it further
        // and potentially cause spurious errors to be issued.
        if (context.scope->isUninstantiated())
            uninstantiatedSpecMap.emplace(key, classType);
        else
            specMap.emplace(key, classType);
    }

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
        auto typeRestriction = ForwardTypeRestriction::Class;
        if (isInterface)
            typeRestriction = ForwardTypeRestriction::InterfaceClass;
        firstForward->checkType(typeRestriction, Visibility::Public, location);
    }
}

void GenericClassDefSymbol::addParameterDecl(const DefinitionSymbol::ParameterDecl& decl) {
    paramDecls.push_back(decl);
}

void GenericClassDefSymbol::serializeTo(ASTSerializer& serializer) const {
    if (firstForward)
        serializer.write("forward", *firstForward);
    serializer.startArray("specializations");
    for (auto&& spec : specializations())
        serializer.serialize(spec, /* inMembersArray */ true);
    serializer.endArray();
}

namespace detail {

ClassSpecializationKey::ClassSpecializationKey(const GenericClassDefSymbol& def,
                                               std::span<const ConstantValue* const> paramValues,
                                               std::span<const Type* const> typeParams) :
    definition(&def), paramValues(paramValues), typeParams(typeParams) {

    // Precompute the hash.
    size_t h = 0;
    hash_combine(h, definition);
    for (auto val : paramValues)
        hash_combine(h, val ? val->hash() : 0);
    for (auto type : typeParams)
        hash_combine(h, type ? type->hash() : 0);
    savedHash = h;
}

bool ClassSpecializationKey::operator==(const ClassSpecializationKey& other) const {
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

} // namespace detail

ConstraintBlockSymbol::ConstraintBlockSymbol(Compilation& c, std::string_view name,
                                             SourceLocation loc) :
    Symbol(SymbolKind::ConstraintBlock, name, loc), Scope(c, this) {
}

static void addSpecifierFlags(const SyntaxList<ClassSpecifierSyntax>& specifiers,
                              bitmask<ConstraintBlockFlags>& flags) {
    for (auto specifier : specifiers) {
        if (!specifier->keyword.isMissing()) {
            switch (specifier->keyword.kind) {
                case TokenKind::InitialKeyword:
                    flags |= ConstraintBlockFlags::Initial;
                    break;
                case TokenKind::ExtendsKeyword:
                    flags |= ConstraintBlockFlags::Extends;
                    break;
                case TokenKind::FinalKeyword:
                    flags |= ConstraintBlockFlags::Final;
                    break;
                default:
                    SLANG_UNREACHABLE;
            }
        }
    }
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

    if (scope.asSymbol().kind != SymbolKind::ClassType)
        scope.addDiag(diag::ConstraintNotInClass, syntax.sourceRange());

    auto nameToken = syntax.name->getLastToken();
    auto result = comp.emplace<ConstraintBlockSymbol>(comp, nameToken.valueText(),
                                                      nameToken.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    // Static is the only allowed qualifier.
    for (auto qual : syntax.qualifiers) {
        if (qual.kind == TokenKind::StaticKeyword)
            result->flags |= ConstraintBlockFlags::Static;
        else if (qual.kind == TokenKind::PureKeyword || qual.kind == TokenKind::ExternKeyword) {
            // This is an error, pure and extern declarations can't declare bodies.
            scope.addDiag(diag::UnexpectedConstraintBlock, syntax.block->sourceRange())
                << qual.range();
            break;
        }
    }

    addSpecifierFlags(syntax.specifiers, result->flags);

    if (!result->flags.has(ConstraintBlockFlags::Static) &&
        scope.asSymbol().kind == SymbolKind::ClassType) {
        result->addThisVar(scope.asSymbol().as<ClassType>());
    }

    return result;
}

ConstraintBlockSymbol& ConstraintBlockSymbol::fromSyntax(const Scope& scope,
                                                         const ConstraintPrototypeSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto nameToken = syntax.name->getLastToken();
    auto result = comp.emplace<ConstraintBlockSymbol>(comp, nameToken.valueText(),
                                                      nameToken.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    result->flags |= ConstraintBlockFlags::Extern;

    addSpecifierFlags(syntax.specifiers, result->flags);

    for (auto qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::StaticKeyword:
                result->flags |= ConstraintBlockFlags::Static;
                break;
            case TokenKind::ExternKeyword:
                result->flags |= ConstraintBlockFlags::ExplicitExtern;
                break;
            case TokenKind::PureKeyword:
                result->flags |= ConstraintBlockFlags::Pure;
                break;
            default:
                break;
        }
    }

    if (scope.asSymbol().kind == SymbolKind::ClassType) {
        auto& classType = scope.asSymbol().as<ClassType>();
        if (result->flags.has(ConstraintBlockFlags::Pure) && !classType.isAbstract)
            scope.addDiag(diag::PureConstraintInAbstract, nameToken.range());

        if (!result->flags.has(ConstraintBlockFlags::Static))
            result->addThisVar(classType);
    }

    return *result;
}

const Constraint& ConstraintBlockSymbol::getConstraints() const {
    if (constraint)
        return *constraint;

    auto syntax = getSyntax();
    auto scope = getParentScope();
    SLANG_ASSERT(syntax && scope);
    ASTContext context(*this, LookupLocation::max);

    if (syntax->kind == SyntaxKind::ConstraintPrototype) {
        // The out-of-block definition must be in our parent scope.
        auto& parentSym = scope->asSymbol();
        auto& outerScope = *parentSym.getParentScope();
        auto& comp = outerScope.getCompilation();

        auto [declSyntax, index, used] = comp.findOutOfBlockDecl(outerScope, parentSym.name, name);
        if (!declSyntax || declSyntax->kind != SyntaxKind::ConstraintDeclaration || name.empty()) {
            if (!flags.has(ConstraintBlockFlags::Pure) && !name.empty()) {
                DiagCode code = flags.has(ConstraintBlockFlags::ExplicitExtern)
                                    ? diag::NoMemberImplFound
                                    : diag::NoConstraintBody;
                outerScope.addDiag(code, location) << name;
            }
            constraint = scope->getCompilation().emplace<InvalidConstraint>(nullptr);
            return *constraint;
        }

        auto& cds = declSyntax->as<ConstraintDeclarationSyntax>();
        *used = true;

        if (flags.has(ConstraintBlockFlags::Pure)) {
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

        if (declStatic != flags.has(ConstraintBlockFlags::Static)) {
            auto& diag = outerScope.addDiag(diag::MismatchStaticConstraint,
                                            cds.getFirstToken().location());
            diag.addNote(diag::NoteDeclarationHere, location);
        }

        bitmask<ConstraintBlockFlags> declFlags;
        addSpecifierFlags(cds.specifiers, declFlags);

        if (declFlags != (flags & (ConstraintBlockFlags::Initial | ConstraintBlockFlags::Extends |
                                   ConstraintBlockFlags::Final))) {
            auto& diag = outerScope.addDiag(diag::MismatchConstraintSpecifiers,
                                            cds.name->getLastToken().location());
            diag.addNote(diag::NoteDeclarationHere, location);
        }

        constraint = &Constraint::bind(*cds.block, context);
        return *constraint;
    }

    constraint = &Constraint::bind(*syntax->as<ConstraintDeclarationSyntax>().block, context);
    return *constraint;
}

static std::string flagsToStr(bitmask<ConstraintBlockFlags> flags) {
    std::string str;
    if (flags.has(ConstraintBlockFlags::Pure))
        str += "pure,";
    if (flags.has(ConstraintBlockFlags::Static))
        str += "static,";
    if (flags.has(ConstraintBlockFlags::Extern))
        str += "extern,";
    if (flags.has(ConstraintBlockFlags::ExplicitExtern))
        str += "explicitExtern,";
    if (flags.has(ConstraintBlockFlags::Initial))
        str += "initial,";
    if (flags.has(ConstraintBlockFlags::Extends))
        str += "extends,";
    if (flags.has(ConstraintBlockFlags::Final))
        str += "final,";
    if (!str.empty())
        str.pop_back();
    return str;
}

void ConstraintBlockSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("constraints", getConstraints());
    if (flags)
        serializer.write("flags", flagsToStr(flags));
}

void ConstraintBlockSymbol::addThisVar(const Type& type) {
    auto tv = getCompilation().emplace<VariableSymbol>("this", type.location,
                                                       VariableLifetime::Automatic);
    tv->setType(type);
    tv->flags |= VariableFlags::Const | VariableFlags::CompilerGenerated;
    thisVar = tv;
    addMember(*thisVar);
}

} // namespace slang::ast
