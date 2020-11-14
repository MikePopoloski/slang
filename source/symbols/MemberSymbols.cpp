//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/MemberSymbols.h"

#include "slang/binding/Expression.h"
#include "slang/binding/FormatHelpers.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/util/StackContainer.h"

namespace slang {

EmptyMemberSymbol& EmptyMemberSymbol::fromSyntax(Compilation& compilation, const Scope& scope,
                                                 const EmptyMemberSyntax& syntax) {
    auto result = compilation.emplace<EmptyMemberSymbol>(syntax.semi.location());
    result->setAttributes(scope, syntax.attributes);

    // Report a warning if this is just an empty semicolon hanging out for no reason,
    // but don't report if this was inserted due to an error elsewhere.
    if (syntax.attributes.empty() && !syntax.semi.isMissing()) {
        // If there are skipped nodes behind this semicolon don't report the warning,
        // as it's likely it's due to the error itself.
        bool anySkipped = false;
        for (auto trivia : syntax.getFirstToken().trivia()) {
            if (trivia.kind == TriviaKind::SkippedTokens) {
                anySkipped = true;
                break;
            }
        }

        if (!anySkipped)
            scope.addDiag(diag::EmptyMember, syntax.sourceRange());
    }

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

void ExplicitImportSymbol::serializeTo(ASTSerializer& serializer) const {
    if (auto pkg = package())
        serializer.writeLink("package", *pkg);

    if (auto sym = importedSymbol())
        serializer.writeLink("import", *sym);
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

void WildcardImportSymbol::serializeTo(ASTSerializer& serializer) const {
    if (auto pkg = getPackage())
        serializer.writeLink("package", *pkg);
}

const Statement& SubroutineSymbol::getBody(EvalContext* evalContext) const {
    BindContext context(*this, LookupLocation::max, BindFlags::ProceduralStatement);
    context.evalContext = evalContext;
    return binder.getStatement(context);
}

SubroutineSymbol* SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const FunctionDeclarationSyntax& syntax,
                                               const Scope& parent, bool outOfBlock) {
    // If this subroutine has a scoped name, it should be an out of block declaration.
    // We shouldn't create a symbol now, since we need the class prototype to hook
    // us in to the correct scope. Register this syntax with the compilation so that
    // it can later be found by the prototype.
    auto proto = syntax.prototype;
    if (!outOfBlock && proto->name->kind == SyntaxKind::ScopedName) {
        // Remember the location in the parent scope where we *would* have inserted this
        // subroutine, for later use during lookup.
        uint32_t index = 1;
        if (auto last = parent.getLastMember())
            index = (uint32_t)last->getIndex() + 1;

        compilation.addOutOfBlockMethod(parent, syntax, SymbolIndex(index));
        return nullptr;
    }

    Token nameToken = proto->name->getLastToken();
    auto lifetime = SemanticFacts::getVariableLifetime(proto->lifetime);
    if (!lifetime.has_value()) {
        // Walk up to the nearest instance and use its default lifetime.
        // If we're not within an instance, default to static.
        lifetime = VariableLifetime::Static;
        auto scope = &parent;
        do {
            auto& sym = scope->asSymbol();
            if (sym.kind == SymbolKind::InstanceBody) {
                lifetime = sym.as<InstanceBodySymbol>().getDefinition().defaultLifetime;
                break;
            }
            else if (sym.kind == SymbolKind::ClassType) {
                lifetime = VariableLifetime::Automatic;
                break;
            }
            scope = sym.getParentScope();
        } while (scope);
    }

    auto subroutineKind = syntax.kind == SyntaxKind::TaskDeclaration ? SubroutineKind::Task
                                                                     : SubroutineKind::Function;
    auto result = compilation.emplace<SubroutineSymbol>(
        compilation, nameToken.valueText(), nameToken.location(), *lifetime, subroutineKind);

    result->setSyntax(syntax);
    result->setAttributes(parent, syntax.attributes);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto->portList)
        buildArguments(*result, *proto->portList, *lifetime, arguments);

    // Subroutines can also declare arguments inside their bodies as port declarations.
    // Let's go looking for them. They're required to be declared before any other statements.
    bool portListError = false;
    for (auto item : syntax.items) {
        if (StatementSyntax::isKind(item->kind))
            break;

        if (item->kind != SyntaxKind::PortDeclaration)
            continue;

        auto& portDecl = item->as<PortDeclarationSyntax>();
        if (portDecl.header->kind != SyntaxKind::VariablePortHeader) {
            parent.addDiag(diag::ExpectedFunctionPort, portDecl.header->sourceRange());
            continue;
        }

        if (!portListError && proto->portList) {
            auto& diag = parent.addDiag(diag::MixingSubroutinePortKinds, portDecl.sourceRange());
            diag.addNote(diag::NoteDeclarationHere, proto->portList->getFirstToken().location());
            portListError = true;
        }

        // TODO: const ref is not currently handled by parser
        auto& header = portDecl.header->as<VariablePortHeaderSyntax>();
        ArgumentDirection direction;
        switch (header.direction.kind) {
            case TokenKind::InputKeyword:
                direction = ArgumentDirection::In;
                break;
            case TokenKind::OutputKeyword:
                direction = ArgumentDirection::Out;
                break;
            case TokenKind::InOutKeyword:
                direction = ArgumentDirection::InOut;
                break;
            case TokenKind::RefKeyword:
                direction = ArgumentDirection::Ref;
                break;
            default:
                THROW_UNREACHABLE;
        }

        for (auto declarator : portDecl.declarators) {
            auto arg = compilation.emplace<FormalArgumentSymbol>(
                declarator->name.valueText(), declarator->name.location(), direction, *lifetime);
            arg->setDeclaredType(*header.dataType);
            arg->setFromDeclarator(*declarator);
            arg->setAttributes(*result, syntax.attributes);

            result->addMember(*arg);
            arguments.append(arg);
        }
    }

    // The function gets an implicit variable inserted that represents the return value.
    if (subroutineKind == SubroutineKind::Function) {
        auto implicitReturnVar = compilation.emplace<VariableSymbol>(result->name, result->location,
                                                                     VariableLifetime::Automatic);
        implicitReturnVar->setDeclaredType(*proto->returnType);
        implicitReturnVar->isCompilerGenerated = true;
        result->addMember(*implicitReturnVar);
        result->returnValVar = implicitReturnVar;
        result->declaredReturnType.setTypeSyntax(*proto->returnType);
    }
    else {
        result->declaredReturnType.setType(compilation.getVoidType());
    }

    result->arguments = arguments.copy(compilation);
    result->binder.setItems(*result, syntax.items, syntax.sourceRange(), /* inLoop */ false);
    return result;
}

SubroutineSymbol* SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const ClassMethodDeclarationSyntax& syntax,
                                               const Scope& parent) {
    auto result = fromSyntax(compilation, *syntax.declaration, parent, /* outOfBlock */ false);
    if (!result)
        return nullptr;

    result->setAttributes(parent, syntax.attributes);

    for (Token qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::LocalKeyword:
                result->visibility = Visibility::Local;
                break;
            case TokenKind::ProtectedKeyword:
                result->visibility = Visibility::Protected;
                break;
            case TokenKind::StaticKeyword:
                result->flags |= MethodFlags::Static;
                break;
            case TokenKind::PureKeyword:
                // This is unreachable in valid code, because a pure method cannot
                // have an implementation body. The parser checks this for us.
                result->flags |= MethodFlags::Pure;
                break;
            case TokenKind::VirtualKeyword:
                result->flags |= MethodFlags::Virtual;
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

    if (result->name == "new")
        result->flags |= MethodFlags::Constructor;

    if ((result->flags & MethodFlags::Static) == 0)
        result->addThisVar(parent.asSymbol().as<ClassType>());

    return result;
}

SubroutineSymbol& SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const DPIImportSyntax& syntax, const Scope& parent) {
    auto& proto = *syntax.method;
    Token nameToken = proto.name->getLastToken();
    auto subroutineKind = proto.keyword.kind == TokenKind::TaskKeyword ? SubroutineKind::Task
                                                                       : SubroutineKind::Function;

    auto result = compilation.emplace<SubroutineSymbol>(
        compilation, nameToken.valueText(), nameToken.location(), VariableLifetime::Automatic,
        subroutineKind);
    result->setSyntax(syntax);
    result->setAttributes(parent, syntax.attributes);
    result->flags = MethodFlags::DPIImport;

    if (subroutineKind == SubroutineKind::Function)
        result->declaredReturnType.setTypeSyntax(*proto.returnType);
    else
        result->declaredReturnType.setType(compilation.getVoidType());

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto.portList) {
        SubroutineSymbol::buildArguments(*result, *proto.portList, VariableLifetime::Automatic,
                                         arguments);
    }

    result->arguments = arguments.copy(compilation);
    return *result;
}

static bool isSameExpr(const SyntaxNode& l, const SyntaxNode& r) {
    size_t childCount = l.getChildCount();
    if (l.kind != r.kind || childCount != r.getChildCount())
        return false;

    for (size_t i = 0; i < childCount; i++) {
        auto ln = l.childNode(i);
        auto rn = r.childNode(i);
        if (bool(ln) != bool(rn))
            return false;

        if (ln) {
            if (!isSameExpr(*ln, *rn))
                return false;
        }
        else {
            Token lt = l.childToken(i);
            Token rt = r.childToken(i);
            if (lt.kind != rt.kind || lt.valueText() != rt.valueText())
                return false;
        }
    }
    return true;
}

SubroutineSymbol& SubroutineSymbol::createOutOfBlock(Compilation& compilation,
                                                     const FunctionDeclarationSyntax& syntax,
                                                     const MethodPrototypeSymbol& prototype,
                                                     const Scope& parent,
                                                     const Scope& definitionScope,
                                                     SymbolIndex outOfBlockIndex) {
    auto result = fromSyntax(compilation, syntax, parent, /* outOfBlock */ true);
    ASSERT(result);

    // Set the parent pointer of the new subroutine so that lookups work correctly.
    // We won't actually exist in the scope's name map or be iterable through its members,
    // but nothing should be trying to look for these that way anyway.
    result->setParent(parent, SymbolIndex(INT32_MAX));
    result->outOfBlockIndex = outOfBlockIndex;

    // All of our flags are taken from the prototype.
    result->visibility = prototype.visibility;
    result->flags = prototype.flags;

    if ((result->flags & MethodFlags::Static) == 0)
        result->addThisVar(parent.asSymbol().as<ClassType>());

    if (!prototype.checkMethodMatch(parent, *result))
        return *result;

    // The return type is not allowed to use a simple name to access class members.
    auto& defRetType = result->getReturnType();
    if (defRetType.getParentScope() == &parent) {
        auto retName = SyntaxFacts::getSimpleTypeName(*syntax.prototype->returnType);
        if (!retName.empty()) {
            // Repeat the lookup for the type but in the definition scope instead of the
            // class scope. If we find a type symbol that matches what we already looked up,
            // there's no problem. Otherwise, this is an error.
            auto found = Lookup::unqualified(definitionScope, retName);
            if (!found || found->getIndex() > outOfBlockIndex || !found->isType() ||
                !found->as<Type>().isMatching(defRetType)) {
                auto& diag = parent.addDiag(diag::MethodReturnTypeScoped,
                                            syntax.prototype->returnType->sourceRange());
                diag << result->name;
                diag << parent.asSymbol().name;
                return *result;
            }
        }
    }

    // Handle default value expressions.
    auto defArgs = result->arguments;
    auto protoArgs = prototype.arguments;
    for (auto di = defArgs.begin(), pi = protoArgs.begin(); di != defArgs.end(); di++, pi++) {
        // If the definition provides a default value for an argument, the prototype
        // must also have that default, and they must be identical expressions.
        // If the definition does't provide a default but the prototype does, copy
        // that default into the definition.
        const FormalArgumentSymbol* da = *di;
        const FormalArgumentSymbol* pa = *pi;
        const Expression* de = da->getInitializer();
        const Expression* pe = pa->getInitializer();
        if (de) {
            if (!pe) {
                auto& diag = parent.addDiag(diag::MethodArgNoDefault, de->sourceRange);
                diag << da->name;
                diag.addNote(diag::NoteDeclarationHere, pa->location);
                return *result;
            }
            else if (de->syntax && pe->syntax) {
                // Check for "syntactically identical" expressions.
                if (!isSameExpr(*de->syntax, *pe->syntax)) {
                    auto& diag = parent.addDiag(diag::MethodArgDefaultMismatch, de->sourceRange);
                    diag << da->name;
                    diag.addNote(diag::NoteDeclarationHere, pa->location) << pe->sourceRange;
                    return *result;
                }
            }
        }
        else if (pe) {
            // Copy the prototype default into the definition. The const_cast here is gross
            // but ok since we literally just created these symbols when we called fromSyntax().
            // NOTE: there is an ambiguity here -- we could copy the bound expression, or we
            // could copy the expression syntax nodes and re-bind them in the context of the
            // definition. This has subtle effects for cases like:
            //
            //   localparam int k = 1;
            //
            //   class C;
            //     extern function int foo(int i = k);
            //     localparam int k = 2;
            //   endclass
            //
            //   function int C::foo(int i);
            //     return i;
            //   endfunction
            //
            // Does foo have a default of 1 or 2? Other simulators disagree with each other
            // and can say either result. I think it makes most sense for the default to
            // come from the prototype's context, so that's what I do here.
            const_cast<FormalArgumentSymbol*>(da)->setInitializer(*pe);
        }
    }

    return *result;
}

static span<const FormalArgumentSymbol* const> cloneArguments(
    Compilation& compilation, Scope& newParent, span<const FormalArgumentSymbol* const> source) {

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments(source.size());
    for (auto arg : source) {
        auto copied = compilation.emplace<FormalArgumentSymbol>(arg->name, arg->location,
                                                                arg->direction, arg->lifetime);
        copied->isCompilerGenerated = arg->isCompilerGenerated;
        copied->isConstant = arg->isConstant;
        copied->getDeclaredType()->copyTypeFrom(*arg->getDeclaredType());
        if (auto init = arg->getDeclaredType()->getInitializer())
            copied->getDeclaredType()->setInitializer(*init);

        newParent.addMember(*copied);
        arguments.append(copied);
    }

    return arguments.copy(compilation);
}

SubroutineSymbol& SubroutineSymbol::createFromPrototype(Compilation& compilation,
                                                        const MethodPrototypeSymbol& prototype,
                                                        const Scope& parent) {
    // Create a stub subroutine symbol that exists only to allow the normal expression
    // machinery to call it (checking argument types, return values, etc).
    auto result = compilation.emplace<SubroutineSymbol>(
        compilation, prototype.name, prototype.location, VariableLifetime::Automatic,
        prototype.subroutineKind);

    result->setParent(parent, SymbolIndex(INT32_MAX));
    result->declaredReturnType.copyTypeFrom(prototype.declaredReturnType);
    result->visibility = prototype.visibility;
    result->flags = prototype.flags;
    result->arguments = cloneArguments(compilation, *result, prototype.arguments);
    return *result;
}

void SubroutineSymbol::setOverride(const SubroutineSymbol& parentMethod) const {
    overrides = &parentMethod;

    auto scope = getParentScope();
    ASSERT(scope);

    checkVirtualMethodMatch(*scope, parentMethod, *this, /* allowDerivedReturn */ true);
}

void SubroutineSymbol::checkVirtualMethodMatch(const Scope& scope,
                                               const SubroutineSymbol& parentMethod,
                                               const SubroutineSymbol& derivedMethod,
                                               bool allowDerivedReturn) {
    auto& retType = derivedMethod.getReturnType();
    auto& parentRetType = parentMethod.getReturnType();
    if (retType.isError() || parentRetType.isError())
        return;

    // Check that return type and arguments match what was declared in the superclass method.
    // If the return type is a class type, it can be one that derives from the return type
    // declared in the superclass method.
    if (!retType.isMatching(parentRetType) && (!allowDerivedReturn || !retType.isClass() ||
                                               !parentRetType.isAssignmentCompatible(retType))) {
        Diagnostic* diag;
        auto typeSyntax = derivedMethod.declaredReturnType.getTypeSyntax();
        if (typeSyntax)
            diag = &scope.addDiag(diag::VirtualReturnMismatch, typeSyntax->sourceRange());
        else
            diag = &scope.addDiag(diag::VirtualReturnMismatch, derivedMethod.location);

        (*diag) << retType;
        (*diag) << derivedMethod.name;
        (*diag) << parentRetType;
        diag->addNote(diag::NoteDeclarationHere, parentMethod.location);
        return;
    }

    auto parentArgs = parentMethod.arguments;
    if (derivedMethod.arguments.size() != parentArgs.size()) {
        auto& diag = scope.addDiag(diag::VirtualArgCountMismatch, derivedMethod.location);
        diag << derivedMethod.name;
        diag.addNote(diag::NoteDeclarationHere, parentMethod.location);
        return;
    }

    for (auto di = derivedMethod.arguments.begin(), pi = parentArgs.begin();
         di != derivedMethod.arguments.end(); di++, pi++) {
        // Names must be identical.
        const FormalArgumentSymbol* da = *di;
        const FormalArgumentSymbol* pa = *pi;
        if (da->name != pa->name && !da->name.empty() && !pa->name.empty()) {
            auto& diag = scope.addDiag(diag::VirtualArgNameMismatch, da->location);
            diag << da->name << pa->name;
            diag.addNote(diag::NoteDeclarationHere, pa->location);
            return;
        }

        // Types must match.
        const Type& dt = da->getType();
        const Type& pt = pa->getType();
        if (!dt.isMatching(pt) && !dt.isError() && !pt.isError()) {
            auto& diag = scope.addDiag(diag::VirtualArgTypeMismatch, da->location);
            diag << da->name << dt << pt;
            diag.addNote(diag::NoteDeclarationHere, pa->location);
            return;
        }

        // Direction must match.
        if (da->direction != pa->direction) {
            auto& diag = scope.addDiag(diag::VirtualArgDirectionMismatch, da->location);
            diag << da->name;
            diag.addNote(diag::NoteDeclarationHere, pa->location);
            return;
        }

        // The presence of a default value must be the same.
        const Expression* de = da->getInitializer();
        const Expression* pe = pa->getInitializer();
        if (bool(de) != bool(pe)) {
            if (de) {
                auto& diag = scope.addDiag(diag::VirtualArgNoParentDefault, de->sourceRange);
                diag << da->name;
                diag.addNote(diag::NoteDeclarationHere, pa->location);
            }
            else {
                auto& diag = scope.addDiag(diag::VirtualArgNoDerivedDefault, da->location);
                diag << da->name;
                diag.addNote(diag::NoteDeclarationHere, pa->location);
            }
            return;
        }
    }
}

void SubroutineSymbol::buildArguments(Scope& scope, const FunctionPortListSyntax& syntax,
                                      VariableLifetime defaultLifetime,
                                      SmallVector<const FormalArgumentSymbol*>& arguments) {
    auto& comp = scope.getCompilation();
    const DataTypeSyntax* lastType = nullptr;
    auto lastDirection = ArgumentDirection::In;

    for (const FunctionPortSyntax* portSyntax : syntax.ports) {
        ArgumentDirection direction;
        bool directionSpecified = true;
        switch (portSyntax->direction.kind) {
            case TokenKind::InputKeyword:
                direction = ArgumentDirection::In;
                break;
            case TokenKind::OutputKeyword:
                direction = ArgumentDirection::Out;
                break;
            case TokenKind::InOutKeyword:
                direction = ArgumentDirection::InOut;
                break;
            case TokenKind::RefKeyword:
                if (portSyntax->constKeyword)
                    direction = ArgumentDirection::ConstRef;
                else
                    direction = ArgumentDirection::Ref;
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
        auto arg = comp.emplace<FormalArgumentSymbol>(
            declarator->name.valueText(), declarator->name.location(), direction, defaultLifetime);

        // If we're given a type, use that. Otherwise, if we were given a
        // direction, default to logic. Otherwise, use the last type.
        if (portSyntax->dataType) {
            arg->setDeclaredType(*portSyntax->dataType);
            lastType = portSyntax->dataType;
        }
        else if (directionSpecified || !lastType) {
            arg->setType(comp.getLogicType());
            lastType = nullptr;
        }
        else {
            arg->setDeclaredType(*lastType);
        }

        arg->setFromDeclarator(*declarator);
        arg->setAttributes(scope, portSyntax->attributes);

        scope.addMember(*arg);
        arguments.append(arg);
        lastDirection = direction;
    }
}

void SubroutineSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("returnType", getReturnType());
    serializer.write("defaultLifetime", toString(defaultLifetime));
    serializer.write("subroutineKind", toString(subroutineKind));
    serializer.write("body", getBody());
    serializer.write("visibility", toString(visibility));

    serializer.startArray("arguments");
    for (auto const arg : arguments) {
        arg->serializeTo(serializer);
    }
    serializer.endArray();
}

void SubroutineSymbol::addThisVar(const Type& type) {
    auto tv = getCompilation().emplace<VariableSymbol>("this", type.location,
                                                       VariableLifetime::Automatic);
    tv->setType(type);
    tv->isConstant = true;
    tv->isCompilerGenerated = true;
    thisVar = tv;
    addMember(*thisVar);
}

MethodPrototypeSymbol::MethodPrototypeSymbol(Compilation& compilation, string_view name,
                                             SourceLocation loc, SubroutineKind subroutineKind,
                                             Visibility visibility, bitmask<MethodFlags> flags) :
    Symbol(SymbolKind::MethodPrototype, name, loc),
    Scope(compilation, this), declaredReturnType(*this), subroutineKind(subroutineKind),
    visibility(visibility), flags(flags) {
}

MethodPrototypeSymbol& MethodPrototypeSymbol::fromSyntax(const Scope& scope,
                                                         const ClassMethodPrototypeSyntax& syntax) {
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

    auto result = comp.emplace<MethodPrototypeSymbol>(
        comp, nameToken.valueText(), nameToken.location(), subroutineKind, visibility, flags);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    if (subroutineKind == SubroutineKind::Function)
        result->declaredReturnType.setTypeSyntax(*proto.returnType);
    else
        result->declaredReturnType.setType(comp.getVoidType());

    // Pure virtual methods can only appear in virtual or interface classes.
    if (flags & MethodFlags::Pure) {
        auto& classType = scope.asSymbol().as<ClassType>();
        if (!classType.isAbstract && !classType.isInterface) {
            scope.addDiag(diag::PureInAbstract, nameToken.range());
            flags &= ~MethodFlags::Pure;
        }
    }

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto.portList) {
        SubroutineSymbol::buildArguments(*result, *proto.portList, VariableLifetime::Automatic,
                                         arguments);
    }

    result->arguments = arguments.copy(comp);
    return *result;
}

MethodPrototypeSymbol& MethodPrototypeSymbol::fromSyntax(
    const Scope& scope, const ModportSubroutinePortSyntax& syntax) {

    auto& comp = scope.getCompilation();
    auto& proto = *syntax.prototype;

    Token nameToken = proto.name->getLastToken();
    auto subroutineKind = proto.keyword.kind == TokenKind::TaskKeyword ? SubroutineKind::Task
                                                                       : SubroutineKind::Function;

    auto result = comp.emplace<MethodPrototypeSymbol>(
        comp, nameToken.valueText(), nameToken.location(), subroutineKind, Visibility::Public,
        MethodFlags::InterfaceImport);
    result->setSyntax(syntax);

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

MethodPrototypeSymbol& MethodPrototypeSymbol::fromSyntax(const Scope& scope,
                                                         LookupLocation lookupLocation,
                                                         const ModportNamedPortSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto name = syntax.name;
    auto result = comp.emplace<MethodPrototypeSymbol>(comp, name.valueText(), name.location(),
                                                      SubroutineKind::Function, Visibility::Public,
                                                      MethodFlags::InterfaceImport);
    result->setSyntax(syntax);

    // Find the target subroutine that is being imported.
    auto target = Lookup::unqualifiedAt(scope, syntax.name.valueText(), lookupLocation,
                                        syntax.name.range(), LookupFlags::NoParentScope);
    if (!target)
        return *result;

    // Target must actually be a subroutine (or a prototype of one).
    if (target->kind != SymbolKind::Subroutine && target->kind != SymbolKind::MethodPrototype) {
        auto& diag = scope.addDiag(diag::NotASubroutine, name.range());
        diag << target->name;
        diag.addNote(diag::NoteDeclarationHere, target->location);
        return *result;
    }

    // Copy details from the found subroutine into the newly created prototype.
    // This lambda exists to handle both SubroutineSymbols and MethodPrototypeSymbols.
    auto copyDetails = [&](auto& source) {
        result->declaredReturnType.copyTypeFrom(source.declaredReturnType);
        result->subroutineKind = source.subroutineKind;
        result->arguments = cloneArguments(comp, *result, source.arguments);
    };

    if (target->kind == SymbolKind::Subroutine)
        copyDetails(target->as<SubroutineSymbol>());
    else
        copyDetails(target->as<MethodPrototypeSymbol>());

    return *result;
}

const SubroutineSymbol* MethodPrototypeSymbol::getSubroutine() const {
    if (subroutine)
        return *subroutine;

    ASSERT(getParentScope() && getParentScope()->asSymbol().getParentScope());
    auto& parentSym = getParentScope()->asSymbol();
    auto& scope = *parentSym.getParentScope();
    auto& comp = scope.getCompilation();

    if (flags.has(MethodFlags::InterfaceImport)) {
        // This is a prototype declared in a modport or an interface. If it's in a
        // modport, check whether the parent interface declares the method already.
        if (parentSym.kind == SymbolKind::Modport) {
            auto result = Lookup::unqualified(
                scope, name, LookupFlags::NoParentScope | LookupFlags::AllowDeclaredAfter);

            if (result) {
                // If we found a symbol, make sure it's actually a subroutine.
                if (result->kind != SymbolKind::Subroutine &&
                    result->kind != SymbolKind::MethodPrototype) {
                    auto& diag = scope.addDiag(diag::NotASubroutine, location);
                    diag << result->name;
                    diag.addNote(diag::NoteDeclarationHere, result->location);
                }
                else {
                    if (result->kind == SymbolKind::MethodPrototype)
                        subroutine = result->as<MethodPrototypeSymbol>().getSubroutine();
                    else
                        subroutine = &result->as<SubroutineSymbol>();

                    if (*subroutine && !checkMethodMatch(*getParentScope(), *subroutine.value()))
                        subroutine = nullptr;

                    return *subroutine;
                }
            }
        }

        // It's allowed to not have an immediate body for this method anywhere
        // (though it will need to be connected if this method is called at runtime).
        // For now, create a placeholder subroutine to return.
        subroutine = &SubroutineSymbol::createFromPrototype(comp, *this, scope);
        return *subroutine;
    }

    // The out-of-block definition must be in our parent scope.
    auto [syntax, index] = comp.findOutOfBlockMethod(scope, parentSym.name, name);
    if (flags & MethodFlags::Pure) {
        // A pure method should not have a body defined.
        if (syntax) {
            auto& diag = scope.addDiag(diag::BodyForPure, syntax->prototype->name->sourceRange());
            diag.addNote(diag::NoteDeclarationHere, location);
            subroutine = nullptr;
        }
        else {
            // Create a stub subroutine that we can return for callers to reference.
            subroutine = &SubroutineSymbol::createFromPrototype(comp, *this, scope);
        }
        return *subroutine;
    }

    // Otherwise, there must be a body for any declared prototype.
    if (!syntax) {
        scope.addDiag(diag::NoMethodImplFound, location) << name;
        subroutine = nullptr;
        return nullptr;
    }

    // The method definition must be located after the class definition.
    if (index <= parentSym.getIndex()) {
        auto& diag = scope.addDiag(diag::MethodDefinitionBeforeClass,
                                   syntax->prototype->name->getLastToken().location());
        diag << name << parentSym.name;
        diag.addNote(diag::NoteDeclarationHere, parentSym.location);
    }

    subroutine =
        &SubroutineSymbol::createOutOfBlock(comp, *syntax, *this, *getParentScope(), scope, index);
    return *subroutine;
}

bool MethodPrototypeSymbol::checkMethodMatch(const Scope& scope,
                                             const SubroutineSymbol& method) const {
    // Check that return type and arguments match what was declared in the prototype.
    auto& protoRetType = getReturnType();
    auto& defRetType = method.getReturnType();
    if (!defRetType.isMatching(protoRetType) && !defRetType.isError() && !protoRetType.isError()) {
        Diagnostic* diag;
        auto typeSyntax = declaredReturnType.getTypeSyntax();
        if (typeSyntax)
            diag = &scope.addDiag(diag::MethodReturnMismatch, typeSyntax->sourceRange());
        else
            diag = &scope.addDiag(diag::MethodReturnMismatch, location);

        (*diag) << defRetType;
        (*diag) << method.name;
        (*diag) << protoRetType;
        diag->addNote(diag::NoteDeclarationHere, method.location);
        return false;
    }

    auto defArgs = method.arguments;
    auto protoArgs = arguments;
    if (defArgs.size() != protoArgs.size()) {
        auto& diag = scope.addDiag(diag::MethodArgCountMismatch, method.location);
        diag << name;
        diag.addNote(diag::NoteDeclarationHere, location);
        return false;
    }

    for (auto di = defArgs.begin(), pi = protoArgs.begin(); di != defArgs.end(); di++, pi++) {
        // Names must be identical.
        const FormalArgumentSymbol* da = *di;
        const FormalArgumentSymbol* pa = *pi;
        if (da->name != pa->name && !da->name.empty() && !pa->name.empty()) {
            auto& diag = scope.addDiag(diag::MethodArgNameMismatch, da->location);
            diag << da->name << pa->name;
            diag.addNote(diag::NoteDeclarationHere, pa->location);
            return false;
        }

        // Types must match.
        const Type& dt = da->getType();
        const Type& pt = pa->getType();
        if (!dt.isMatching(pt) && !dt.isError() && !pt.isError()) {
            auto& diag = scope.addDiag(diag::MethodArgTypeMismatch, da->location);
            diag << da->name << dt << pt;
            diag.addNote(diag::NoteDeclarationHere, pa->location);
            return false;
        }

        // Direction must match.
        if (da->direction != pa->direction) {
            auto& diag = scope.addDiag(diag::MethodArgDirectionMismatch, da->location);
            diag << da->name;
            diag.addNote(diag::NoteDeclarationHere, pa->location);
            return false;
        }
    }

    return true;
}

void MethodPrototypeSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("returnType", getReturnType());
    serializer.write("subroutineKind", toString(subroutineKind));
    serializer.write("visibility", toString(visibility));

    serializer.startArray("arguments");
    for (auto const arg : arguments) {
        arg->serializeTo(serializer);
    }
    serializer.endArray();
}

ModportPortSymbol::ModportPortSymbol(string_view name, SourceLocation loc,
                                     PortDirection direction) :
    ValueSymbol(SymbolKind::ModportPort, name, loc),
    direction(direction) {
}

ModportPortSymbol& ModportPortSymbol::fromSyntax(const Scope& parent, LookupLocation lookupLocation,
                                                 PortDirection direction,
                                                 const ModportNamedPortSyntax& syntax) {
    auto& comp = parent.getCompilation();
    auto name = syntax.name;
    auto result = comp.emplace<ModportPortSymbol>(name.valueText(), name.location(), direction);
    result->setSyntax(syntax);
    result->internalSymbol = Lookup::unqualifiedAt(parent, name.valueText(), lookupLocation,
                                                   name.range(), LookupFlags::NoParentScope);

    if (result->internalSymbol) {
        if (result->internalSymbol->kind == SymbolKind::Subroutine) {
            auto& diag = parent.addDiag(diag::ExpectedImportExport, name.range());
            diag << name.valueText();
            diag.addNote(diag::NoteDeclarationHere, result->internalSymbol->location);
            result->internalSymbol = nullptr;
        }
        else if (!SemanticFacts::isAllowedInModport(result->internalSymbol->kind)) {
            auto& diag = parent.addDiag(diag::NotAllowedInModport, name.range());
            diag << name.valueText();
            diag.addNote(diag::NoteDeclarationHere, result->internalSymbol->location);
            result->internalSymbol = nullptr;
        }
    }

    if (result->internalSymbol) {
        auto sourceType = result->internalSymbol->getDeclaredType();
        ASSERT(sourceType);
        result->getDeclaredType()->copyTypeFrom(*sourceType);
    }

    return *result;
}

void ModportPortSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("direction", toString(direction));
    if (internalSymbol)
        serializer.writeLink("internalSymbol", *internalSymbol);
}

ModportSymbol::ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Modport, name, loc), Scope(compilation, this) {
}

void ModportSymbol::fromSyntax(const Scope& parent, const ModportDeclarationSyntax& syntax,
                               LookupLocation lookupLocation,
                               SmallVector<const ModportSymbol*>& results) {
    auto& comp = parent.getCompilation();
    for (auto item : syntax.items) {
        auto modport =
            comp.emplace<ModportSymbol>(comp, item->name.valueText(), item->name.location());
        modport->setSyntax(*item);
        modport->setAttributes(parent, syntax.attributes);
        results.append(modport);

        for (auto port : item->ports->ports) {
            switch (port->kind) {
                case SyntaxKind::ModportSimplePortList: {
                    auto& portList = port->as<ModportSimplePortListSyntax>();
                    auto direction = SemanticFacts::getPortDirection(portList.direction.kind);
                    for (auto simplePort : portList.ports) {
                        switch (simplePort->kind) {
                            case SyntaxKind::ModportNamedPort: {
                                auto& mpp = ModportPortSymbol::fromSyntax(
                                    parent, lookupLocation, direction,
                                    simplePort->as<ModportNamedPortSyntax>());
                                mpp.setAttributes(*modport, portList.attributes);
                                modport->addMember(mpp);
                                break;
                            }
                            case SyntaxKind::ModportExplicitPort:
                                parent.addDiag(diag::NotYetSupported, simplePort->sourceRange());
                                break;
                            default:
                                THROW_UNREACHABLE;
                        }
                    }
                    break;
                }
                case SyntaxKind::ModportSubroutinePortList: {
                    auto& portList = port->as<ModportSubroutinePortListSyntax>();
                    if (portList.importExport.kind == TokenKind::ExportKeyword) {
                        // TODO: implement
                    }
                    else {
                        for (auto subPort : portList.ports) {
                            switch (subPort->kind) {
                                case SyntaxKind::ModportNamedPort: {
                                    auto& mps = MethodPrototypeSymbol::fromSyntax(
                                        parent, lookupLocation,
                                        subPort->as<ModportNamedPortSyntax>());
                                    mps.setAttributes(*modport, portList.attributes);
                                    modport->addMember(mps);
                                    break;
                                }
                                case SyntaxKind::ModportSubroutinePort: {
                                    auto& mps = MethodPrototypeSymbol::fromSyntax(
                                        parent, subPort->as<ModportSubroutinePortSyntax>());
                                    mps.setAttributes(*modport, portList.attributes);
                                    modport->addMember(mps);
                                    break;
                                }
                                default:
                                    THROW_UNREACHABLE;
                            }
                        }
                    }
                    break;
                }
                case SyntaxKind::ModportClockingPort:
                    parent.addDiag(diag::NotYetSupported, port->sourceRange());
                    break;
                default:
                    THROW_UNREACHABLE;
            }
        }
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
                                        const ContinuousAssignSyntax& syntax, const Scope& scope,
                                        LookupLocation location,
                                        SmallVector<const Symbol*>& results) {
    BindContext context(scope, location);
    auto& netType = scope.getDefaultNetType();

    for (auto expr : syntax.assignments) {
        // If not explicitly disabled, check for net references on the lhs of each
        // assignment that should create implicit nets.
        if (!netType.isError()) {
            // The expression here should always be an assignment expression unless
            // the program is already ill-formed (diagnosed by the parser).
            if (expr->kind == SyntaxKind::AssignmentExpression) {
                SmallVectorSized<Token, 8> implicitNets;
                Expression::findPotentiallyImplicitNets(*expr->as<BinaryExpressionSyntax>().left,
                                                        context, implicitNets);

                for (Token t : implicitNets) {
                    auto net = compilation.emplace<NetSymbol>(t.valueText(), t.location(), netType);
                    net->setType(compilation.getLogicType());
                    results.append(net);
                }
            }
        }

        auto symbol = compilation.emplace<ContinuousAssignSymbol>(*expr);
        symbol->setAttributes(scope, syntax.attributes);
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

    // TODO: handle drive strengths, delays
    BindContext context(*scope, LookupLocation::before(*this));
    assign =
        &Expression::bind(syntax->as<ExpressionSyntax>(), context, BindFlags::AssignmentAllowed);

    return *assign;
}

void ContinuousAssignSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("assignment", getAssignment());
}

GenvarSymbol::GenvarSymbol(string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Genvar, name, loc) {
}

void GenvarSymbol::fromSyntax(const Scope& parent, const GenvarDeclarationSyntax& syntax,
                              SmallVector<const GenvarSymbol*>& results) {
    auto& comp = parent.getCompilation();
    for (auto id : syntax.identifiers) {
        auto name = id->identifier;
        if (name.valueText().empty())
            continue;

        auto genvar = comp.emplace<GenvarSymbol>(name.valueText(), name.location());
        genvar->setSyntax(*id);
        genvar->setAttributes(parent, syntax.attributes);
        results.append(genvar);
    }
}

namespace {

GateSymbol* createGate(Compilation& compilation, const Scope& scope, GateType gateType,
                       const GateInstanceSyntax& syntax,
                       span<const AttributeInstanceSyntax* const> attributes) {
    string_view name;
    SourceLocation loc;
    if (syntax.decl) {
        name = syntax.decl->name.valueText();
        loc = syntax.decl->name.location();
    }
    else {
        name = "";
        loc = syntax.getFirstToken().location();
    }

    // TODO: ports!

    GateSymbol* gate = compilation.emplace<GateSymbol>(name, loc, gateType);
    gate->setSyntax(syntax);
    gate->setAttributes(scope, attributes);
    return gate;
};

using DimIterator = span<VariableDimensionSyntax*>::iterator;

Symbol* recurseGateArray(Compilation& compilation, GateType gateType,
                         const GateInstanceSyntax& instance, const BindContext& context,
                         DimIterator it, DimIterator end,
                         span<const AttributeInstanceSyntax* const> attributes) {
    if (it == end)
        return createGate(compilation, context.scope, gateType, instance, attributes);

    // Evaluate the dimensions of the array. If this fails for some reason,
    // make up an empty array so that we don't get further errors when
    // things try to reference this symbol.
    auto nameToken = instance.decl->name;
    auto dim = context.evalDimension(**it, /* requireRange */
                                     true, /* isPacked */ false);
    if (!dim.isRange()) {
        return compilation.emplace<GateArraySymbol>(compilation, nameToken.valueText(),
                                                    nameToken.location(),
                                                    span<const Symbol* const>{}, ConstantRange());
    }

    ++it;

    ConstantRange range = dim.range;
    SmallVectorSized<const Symbol*, 8> elements;
    for (int32_t i = range.lower(); i <= range.upper(); i++) {
        auto symbol =
            recurseGateArray(compilation, gateType, instance, context, it, end, attributes);
        symbol->name = "";
        elements.append(symbol);
    }

    auto result = compilation.emplace<GateArraySymbol>(compilation, nameToken.valueText(),
                                                       nameToken.location(),
                                                       elements.copy(compilation), range);
    for (auto element : elements)
        result->addMember(*element);

    return result;
}

} // namespace

void GateSymbol::fromSyntax(Compilation& compilation, const GateInstantiationSyntax& syntax,
                            LookupLocation location, const Scope& scope,
                            SmallVector<const Symbol*>& results) {
    // TODO: strengths and delays
    auto gateType = SemanticFacts::getGateType(syntax.gateType.kind);

    BindContext context(scope, location, BindFlags::Constant);
    for (auto instance : syntax.instances) {
        if (!instance->decl) {
            results.append(createGate(compilation, scope, gateType, *instance, syntax.attributes));
        }
        else {
            auto dims = instance->decl->dimensions;
            auto symbol = recurseGateArray(compilation, gateType, *instance, context, dims.begin(),
                                           dims.end(), syntax.attributes);
            results.append(symbol);
        }
    }
}

void GateSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("gateType", toString(gateType));
}

void GateArraySymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("range", range.toString());
}

ElabSystemTaskSymbol::ElabSystemTaskSymbol(ElabSystemTaskKind taskKind, SourceLocation loc) :
    Symbol(SymbolKind::ElabSystemTask, "", loc), taskKind(taskKind) {
}

ElabSystemTaskSymbol& ElabSystemTaskSymbol::fromSyntax(Compilation& compilation,
                                                       const ElabSystemTaskSyntax& syntax) {
    // Just create the symbol now. The diagnostic will be issued later
    // when someone visit the symbol and asks for it.
    auto taskKind = SemanticFacts::getElabSystemTaskKind(syntax.name);
    auto result = compilation.emplace<ElabSystemTaskSymbol>(taskKind, syntax.name.location());
    result->setSyntax(syntax);
    return *result;
}

string_view ElabSystemTaskSymbol::getMessage() const {
    if (message)
        return *message;

    auto syntax = getSyntax();
    ASSERT(syntax);

    auto empty = [&] {
        message = ""sv;
        return *message;
    };

    auto argSyntax = syntax->as<ElabSystemTaskSyntax>().arguments;
    if (!argSyntax)
        return empty();

    auto scope = getParentScope();
    ASSERT(scope);

    // Bind all arguments.
    auto& comp = scope->getCompilation();
    BindContext bindCtx(*scope, LookupLocation::before(*this), BindFlags::Constant);
    SmallVectorSized<const Expression*, 4> args;
    for (auto arg : argSyntax->parameters) {
        switch (arg->kind) {
            case SyntaxKind::OrderedArgument: {
                const auto& oa = arg->as<OrderedArgumentSyntax>();
                args.append(&Expression::bind(*oa.expr, bindCtx));
                break;
            }
            case SyntaxKind::NamedArgument:
                bindCtx.addDiag(diag::NamedArgNotAllowed, arg->sourceRange());
                return empty();
            case SyntaxKind::EmptyArgument:
                args.append(
                    comp.emplace<EmptyArgumentExpression>(comp.getVoidType(), arg->sourceRange()));
                break;
            default:
                THROW_UNREACHABLE;
        }

        if (args.back()->bad())
            return empty();
    }

    // If this is a $fatal task, check the finish number. We don't use this
    // for anything, but enforce that it's 0, 1, or 2.
    span<const Expression* const> argSpan = args;
    if (taskKind == ElabSystemTaskKind::Fatal && !argSpan.empty()) {
        if (!FmtHelpers::checkFinishNum(bindCtx, *argSpan[0]))
            return empty();

        argSpan = argSpan.subspan(1);
    }

    // Check all arguments.
    if (!FmtHelpers::checkDisplayArgs(bindCtx, argSpan))
        return empty();

    // Format the message to string.
    EvalContext evalCtx(comp);
    optional<std::string> str = FmtHelpers::formatDisplay(*scope, evalCtx, argSpan);
    if (!str)
        return empty();

    str->insert(0, ": ");

    // Copy the string into permanent memory.
    auto mem = comp.allocate(str->size(), alignof(char));
    memcpy(mem, str->data(), str->size());

    message = string_view(reinterpret_cast<char*>(mem), str->size());
    return *message;
}

void ElabSystemTaskSymbol::issueDiagnostic() const {
    auto scope = getParentScope();
    ASSERT(scope);

    DiagCode code;
    switch (taskKind) {
        case ElabSystemTaskKind::Fatal:
            code = diag::FatalTask;
            break;
        case ElabSystemTaskKind::Error:
            code = diag::ErrorTask;
            break;
        case ElabSystemTaskKind::Warning:
            code = diag::WarningTask;
            break;
        case ElabSystemTaskKind::Info:
            code = diag::InfoTask;
            break;
        default:
            THROW_UNREACHABLE;
    }

    scope->addDiag(code, location) << getMessage();
}

void ElabSystemTaskSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("taskKind", toString(taskKind));
    serializer.write("message", getMessage());
}

} // namespace slang
