//------------------------------------------------------------------------------
// SubroutineSymbols.h
// Contains subroutine symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/SubroutineSymbols.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

const Statement& SubroutineSymbol::getBody() const {
    if (!stmt) {
        auto syntax = getSyntax();
        if (!syntax || !FunctionDeclarationSyntax::isKind(syntax->kind)) {
            // DPI functions, subroutines created from prototypes, etc
            // don't have a real body.
            stmt = &StatementList::makeEmpty(getCompilation());
        }
        else if (isConstructing) {
            // Avoid issues with recursive function calls re-entering this
            // method while we're still constructing.
            return InvalidStatement::Instance;
        }
        else {
            isConstructing = true;
            auto guard = ScopeGuard([this] { isConstructing = false; });

            ASTContext context(*this, LookupLocation::max);
            if (subroutineKind == SubroutineKind::Function)
                context.flags |= ASTFlags::Function;

            Statement::StatementContext stmtCtx(context);
            stmtCtx.blocks = blocks;

            stmt = &Statement::bindItems(syntax->as<FunctionDeclarationSyntax>().items, context,
                                         stmtCtx);
        }
    }
    return *stmt;
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

        auto& scopedName = proto->name->as<ScopedNameSyntax>();
        if (scopedName.separator.kind == TokenKind::DoubleColon) {
            // This is an out-of-block class method implementation.
            compilation.addOutOfBlockDecl(parent, scopedName, syntax, SymbolIndex(index));
        }
        else {
            // Otherwise this is an interface method implementation.
            // We should create the method like normal but not add it to
            // the parent name map (because it can only be looked up via
            // the interface instance).
            auto result = SubroutineSymbol::fromSyntax(compilation, syntax, parent,
                                                       /* outOfBlock */ true);
            SLANG_ASSERT(result);

            result->setParent(parent, SymbolIndex(index));
            compilation.addExternInterfaceMethod(*result);
        }
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
            else if (sym.kind == SymbolKind::Package) {
                lifetime = sym.as<PackageSymbol>().defaultLifetime;
                break;
            }
            scope = sym.getParentScope();
        } while (scope);
    }

    auto subroutineKind = syntax.kind == SyntaxKind::TaskDeclaration ? SubroutineKind::Task
                                                                     : SubroutineKind::Function;
    auto result = compilation.emplace<SubroutineSymbol>(compilation, nameToken.valueText(),
                                                        nameToken.location(), *lifetime,
                                                        subroutineKind);

    result->setSyntax(syntax);
    result->setAttributes(parent, syntax.attributes);

    SmallVector<const FormalArgumentSymbol*> arguments;
    if (proto->portList)
        result->flags |= buildArguments(*result, parent, *proto->portList, *lifetime, arguments);

    if (nameToken.kind == TokenKind::NewKeyword) {
        result->flags |= MethodFlags::Constructor;
        result->declaredReturnType.setType(compilation.getVoidType());
    }
    else if (subroutineKind == SubroutineKind::Function) {
        // The function gets an implicit variable inserted that represents the return value.
        auto implicitReturnVar = compilation.emplace<VariableSymbol>(result->name, result->location,
                                                                     VariableLifetime::Automatic);
        implicitReturnVar->setDeclaredType(*proto->returnType);
        implicitReturnVar->flags |= VariableFlags::CompilerGenerated;
        result->addMember(*implicitReturnVar);
        result->returnValVar = implicitReturnVar;
        result->declaredReturnType.setTypeSyntax(*proto->returnType);
    }
    else {
        result->declaredReturnType.setType(compilation.getVoidType());
    }

    const Symbol* last = result->getLastMember();
    result->blocks = Statement::createAndAddBlockItems(*result, syntax.items);

    // Subroutines can also declare arguments inside their bodies as port declarations.
    // Find them by walking through members that were added by setItems().
    if (!last)
        last = result->getFirstMember();
    else
        last = last->getNextSibling();

    bool portListError = false;
    while (last) {
        if (last->kind == SymbolKind::FormalArgument) {
            if (!portListError && proto->portList) {
                auto& diag = parent.addDiag(diag::MixingSubroutinePortKinds, last->location);
                diag.addNote(diag::NoteDeclarationHere,
                             proto->portList->getFirstToken().location());
                portListError = true;
            }

            auto& arg = last->as<FormalArgumentSymbol>();
            arguments.push_back(&arg);

            if (lifetime == VariableLifetime::Static && arg.direction == ArgumentDirection::Ref)
                parent.addDiag(diag::RefArgAutomaticFunc, last->location);
        }
        last = last->getNextSibling();
    }

    result->arguments = arguments.copy(compilation);
    return result;
}

static std::pair<bitmask<MethodFlags>, Visibility> getMethodFlags(
    const TokenList& qualifiers, const FunctionPrototypeSyntax& proto) {

    bitmask<MethodFlags> flags;
    auto visibility = Visibility::Public;
    for (Token qual : qualifiers) {
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
                SLANG_UNREACHABLE;
        }
    }

    for (auto specifier : proto.specifiers) {
        if (!specifier->keyword.isMissing()) {
            switch (specifier->keyword.kind) {
                case TokenKind::InitialKeyword:
                    flags |= MethodFlags::Initial;
                    break;
                case TokenKind::ExtendsKeyword:
                    flags |= MethodFlags::Extends;
                    break;
                case TokenKind::FinalKeyword:
                    flags |= MethodFlags::Final;
                    break;
                default:
                    SLANG_UNREACHABLE;
            }
        }
    }

    return {flags, visibility};
}

SubroutineSymbol* SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const ClassMethodDeclarationSyntax& syntax,
                                               const Scope& parent) {
    auto result = fromSyntax(compilation, *syntax.declaration, parent, /* outOfBlock */ false);
    if (!result)
        return nullptr;

    result->setAttributes(parent, syntax.attributes);

    auto [flags, visibility] = getMethodFlags(syntax.qualifiers, *syntax.declaration->prototype);
    result->visibility = visibility;
    result->flags |= flags;

    if (!result->flags.has(MethodFlags::Static))
        result->addThisVar(parent.asSymbol().as<ClassType>());

    return result;
}

SubroutineSymbol& SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const DPIImportSyntax& syntax, const Scope& parent) {
    auto& proto = *syntax.method;
    Token nameToken = proto.name->getLastToken();
    auto subroutineKind = proto.keyword.kind == TokenKind::TaskKeyword ? SubroutineKind::Task
                                                                       : SubroutineKind::Function;

    auto result = compilation.emplace<SubroutineSymbol>(compilation, nameToken.valueText(),
                                                        nameToken.location(),
                                                        VariableLifetime::Automatic,
                                                        subroutineKind);
    result->setSyntax(syntax);
    result->setAttributes(parent, syntax.attributes);
    result->flags = MethodFlags::DPIImport;

    result->declaredReturnType.addFlags(DeclaredTypeFlags::DPIReturnType);
    if (subroutineKind == SubroutineKind::Function)
        result->declaredReturnType.setTypeSyntax(*proto.returnType);
    else
        result->declaredReturnType.setType(compilation.getVoidType());

    bool isPure = false;
    switch (syntax.property.kind) {
        case TokenKind::PureKeyword:
            isPure = true;
            result->flags |= MethodFlags::Pure;
            break;
        case TokenKind::ContextKeyword:
            result->flags |= MethodFlags::DPIContext;
            break;
        default:
            break;
    }

    if (syntax.specString.valueText() == "DPI")
        parent.addDiag(diag::DPISpecDisallowed, syntax.specString.range());

    SmallVector<const FormalArgumentSymbol*> arguments;
    if (proto.portList) {
        result->flags |= SubroutineSymbol::buildArguments(*result, parent, *proto.portList,
                                                          VariableLifetime::Automatic, arguments);
    }

    // Check arguments for extra rules imposed by DPI imports.
    bool pureError = false;
    for (auto arg : arguments) {
        const_cast<FormalArgumentSymbol*>(arg)->getDeclaredType()->addFlags(
            DeclaredTypeFlags::DPIArg);

        if (arg->direction == ArgumentDirection::Ref)
            parent.addDiag(diag::DPIRefArg, arg->location);
        else if (arg->direction == ArgumentDirection::Out ||
                 arg->direction == ArgumentDirection::InOut) {
            if (isPure && !pureError) {
                parent.addDiag(diag::DPIPureArg, arg->location);
                pureError = true;
            }
        }
    }

    result->arguments = arguments.copy(compilation);
    return *result;
}

SubroutineSymbol& SubroutineSymbol::createOutOfBlock(Compilation& compilation,
                                                     const FunctionDeclarationSyntax& syntax,
                                                     const MethodPrototypeSymbol& prototype,
                                                     const Scope& parent,
                                                     const Scope& definitionScope,
                                                     SymbolIndex outOfBlockIndex) {
    auto result = fromSyntax(compilation, syntax, parent, /* outOfBlock */ true);
    SLANG_ASSERT(result);

    // Set the parent pointer of the new subroutine so that lookups work correctly.
    // We won't actually exist in the scope's name map or be iterable through its members,
    // but nothing should be trying to look for these that way anyway.
    result->setParent(parent, SymbolIndex(INT32_MAX));
    result->outOfBlockIndex = outOfBlockIndex;
    result->prototype = &prototype;

    // All of our flags are taken from the prototype.
    result->visibility = prototype.visibility;
    result->flags = prototype.flags;

    if (prototype.isVirtual())
        result->flags |= MethodFlags::Virtual;

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
    auto protoArgs = prototype.getArguments();
    for (auto di = defArgs.begin(), pi = protoArgs.begin(); di != defArgs.end(); di++, pi++) {
        // If the definition provides a default value for an argument, the prototype
        // must also have that default, and they must be identical expressions.
        // If the definition does't provide a default but the prototype does, copy
        // that default into the definition.
        const FormalArgumentSymbol* da = *di;
        const FormalArgumentSymbol* pa = *pi;
        const Expression* de = da->getDefaultValue();
        const Expression* pe = pa->getDefaultValue();
        if (de) {
            if (!pe) {
                auto& diag = parent.addDiag(diag::MethodArgNoDefault, de->sourceRange);
                diag << da->name;
                diag.addNote(diag::NoteDeclarationHere, pa->location);
                return *result;
            }
            else if (de->syntax && pe->syntax && !de->bad() && !pe->bad()) {
                // Check for "syntactically identical" expressions.
                if (!de->syntax->isEquivalentTo(*pe->syntax)) {
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
            // NOTE: there is an ambiguity here -- we could copy the AST expression, or we
            // could copy the expression syntax nodes and recreate them in the context of the
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
            const_cast<FormalArgumentSymbol*>(da)->setDefaultValue(pe);
        }
    }

    return *result;
}

static std::span<const FormalArgumentSymbol* const> cloneArguments(
    Compilation& compilation, Scope& newParent,
    std::span<const FormalArgumentSymbol* const> source) {

    SmallVector<const FormalArgumentSymbol*> arguments(source.size(), UninitializedTag());
    for (auto arg : source) {
        auto copied = compilation.emplace<FormalArgumentSymbol>(arg->name, arg->location,
                                                                arg->direction, arg->lifetime);
        copied->flags = arg->flags;
        copied->getDeclaredType()->setLink(*arg->getDeclaredType());
        copied->setDefaultValue(arg->getDefaultValue());

        newParent.addMember(*copied);
        arguments.push_back(copied);
    }

    return arguments.copy(compilation);
}

SubroutineSymbol& SubroutineSymbol::createFromPrototype(Compilation& compilation,
                                                        const MethodPrototypeSymbol& prototype,
                                                        const Scope& parent) {
    // Create a stub subroutine symbol that exists only to allow the normal expression
    // machinery to call it (checking argument types, return values, etc).
    auto result = compilation.emplace<SubroutineSymbol>(compilation, prototype.name,
                                                        prototype.location,
                                                        VariableLifetime::Automatic,
                                                        prototype.subroutineKind);

    result->setParent(parent, SymbolIndex(INT32_MAX));
    result->declaredReturnType.setLink(prototype.declaredReturnType);
    result->visibility = prototype.visibility;
    result->flags = prototype.flags;
    result->arguments = cloneArguments(compilation, *result, prototype.getArguments());
    result->prototype = &prototype;
    return *result;
}

void SubroutineSymbol::setOverride(const SubroutineSymbol& parentMethod) const {
    overrides = &parentMethod;

    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    checkVirtualMethodMatch(*scope, parentMethod, *this, /* allowDerivedReturn */ true);
}

void SubroutineSymbol::checkVirtualMethodMatch(const Scope& scope,
                                               const SubroutineSymbol& parentMethod,
                                               const SubroutineSymbol& derivedMethod,
                                               bool allowDerivedReturn) {
    if (parentMethod.subroutineKind != derivedMethod.subroutineKind) {
        auto& diag = scope.addDiag(diag::VirtualKindMismatch, derivedMethod.location);
        diag.addNote(diag::NoteDeclarationHere, parentMethod.location);
        return;
    }

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
        const Expression* de = da->getDefaultValue();
        const Expression* pe = pa->getDefaultValue();
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

    if (parentMethod.visibility != derivedMethod.visibility) {
        auto visStr = [](Visibility vis) {
            switch (vis) {
                case Visibility::Local:
                    return "local"sv;
                case Visibility::Protected:
                    return "protected"sv;
                case Visibility::Public:
                    return "public"sv;
                default:
                    return ""sv;
            }
        };

        auto& diag = scope.addDiag(diag::VirtualVisibilityMismatch, derivedMethod.location);
        diag << derivedMethod.name << visStr(derivedMethod.visibility)
             << visStr(parentMethod.visibility);
        diag.addNote(diag::NoteDeclarationHere, parentMethod.location);
    }
}

struct LocalVarCheckVisitor {
    const Scope& scope;
    const SyntaxNode& syntax;
    std::string_view argName;
    bool anyErrors = false;

    LocalVarCheckVisitor(const Scope& scope, const SyntaxNode& syntax, std::string_view argName) :
        scope(scope), syntax(syntax), argName(argName) {}

    template<typename T>
    void visit(const T& expr) {
        if (anyErrors)
            return;

        if constexpr (std::is_base_of_v<Expression, T>) {
            if (ValueExpressionBase::isKind(expr.kind)) {
                if (auto sym = expr.getSymbolReference();
                    sym && sym->kind == SymbolKind::ClassProperty) {
                    checkVisibility(*sym, expr, sym->template as<ClassPropertySymbol>().visibility);
                }
            }
            else if (expr.kind == ExpressionKind::Call) {
                auto& call = expr.template as<CallExpression>();
                if (!call.isSystemCall()) {
                    auto& sub = *std::get<const SubroutineSymbol*>(call.subroutine);
                    checkVisibility(sub, expr, sub.visibility);
                }
            }

            if constexpr (HasVisitExprs<T, LocalVarCheckVisitor>) {
                expr.visitExprs(*this);
            }
        }
    }

    void checkVisibility(const Symbol& symbol, const Expression& expr, Visibility visibility) {
        if (visibility == Visibility::Local) {
            auto& diag = scope.addDiag(diag::DefaultSuperArgLocalReference, syntax.sourceRange());
            diag << argName << symbol.name;
            diag.addNote(diag::NoteReferencedHere, expr.sourceRange);
            anyErrors = true;
        }
    }
};

void SubroutineSymbol::inheritDefaultedArgList(
    Scope& scope, const Scope& parentScope, const SyntaxNode& syntax,
    SmallVectorBase<const FormalArgumentSymbol*>& arguments) {

    auto& comp = scope.getCompilation();
    if (parentScope.asSymbol().kind == SymbolKind::ClassType) {
        auto& ct = parentScope.asSymbol().as<ClassType>();
        auto baseClass = ct.getBaseClass();
        if (!baseClass) {
            scope.addDiag(diag::SuperNoBase, syntax.sourceRange()) << ct.name;
        }
        else if (baseClass->isClass()) {
            // Note: we check isClass() above to skip over cases where
            // the baseClass is the ErrorType.
            auto& baseCt = baseClass->getCanonicalType().as<ClassType>();
            if (auto constructor = baseCt.getConstructor()) {
                // We found the base class's constructor.
                // Pull in all arguments from it.
                bool anyErrors = false;
                for (auto arg : constructor->getArguments()) {
                    // It's an error if any of the inherited arguments
                    // have default values that refer to local members
                    // of the parent class.
                    if (auto defVal = arg->getDefaultValue();
                        !anyErrors && defVal && !arg->name.empty()) {
                        LocalVarCheckVisitor visitor(scope, syntax, arg->name);
                        defVal->visit(visitor);
                        anyErrors |= visitor.anyErrors;
                    }

                    auto& cloned = arg->clone(comp);
                    scope.addMember(cloned);
                    arguments.push_back(&cloned);
                }
            }
        }
    }
}

bitmask<MethodFlags> SubroutineSymbol::buildArguments(
    Scope& scope, const Scope& parentScope, const FunctionPortListSyntax& syntax,
    VariableLifetime defaultLifetime, SmallVectorBase<const FormalArgumentSymbol*>& arguments) {

    auto& comp = scope.getCompilation();
    const DataTypeSyntax* lastType = nullptr;
    const SyntaxNode* explicitDefault = nullptr;
    auto lastDirection = ArgumentDirection::In;
    bitmask<VariableFlags> lastFlags;
    bitmask<MethodFlags> resultFlags;

    for (auto portBase : syntax.ports) {
        if (portBase->previewNode)
            scope.addMembers(*portBase->previewNode);

        if (portBase->kind == SyntaxKind::DefaultFunctionPort) {
            lastDirection = ArgumentDirection::In;
            lastType = nullptr;

            if (explicitDefault) {
                // Ignore a duplicate default.
                scope.addDiag(diag::MultipleDefaultConstructorArg, portBase->sourceRange());
            }
            else {
                explicitDefault = portBase;
                inheritDefaultedArgList(scope, parentScope, *portBase, arguments);
                resultFlags |= MethodFlags::DefaultedSuperArg;
            }
            continue;
        }

        auto direction = lastDirection;
        auto flags = lastFlags;
        bool directionSpecified = false;
        auto& fps = portBase->as<FunctionPortSyntax>();
        if (fps.direction) {
            directionSpecified = true;
            direction = SemanticFacts::getDirection(fps.direction.kind);
            flags = {};

            if (direction == ArgumentDirection::Ref) {
                if (defaultLifetime == VariableLifetime::Static)
                    scope.addDiag(diag::RefArgAutomaticFunc, fps.direction.range());

                if (fps.constKeyword)
                    flags |= VariableFlags::Const;

                if (fps.staticKeyword)
                    flags |= VariableFlags::RefStatic;
            }
        }

        auto& decl = *fps.declarator;
        auto arg = comp.emplace<FormalArgumentSymbol>(decl.name.valueText(), decl.name.location(),
                                                      direction, defaultLifetime);
        arg->flags |= flags;

        // If we're given a type, use that. Otherwise, if we were given a
        // direction, default to logic. Otherwise, use the last type.
        if (fps.dataType) {
            arg->setDeclaredType(*fps.dataType);
            lastType = fps.dataType;
        }
        else if (directionSpecified || !lastType) {
            arg->setDeclaredType(comp.createEmptyTypeSyntax(decl.getFirstToken().location()));
            lastType = nullptr;
        }
        else {
            arg->setDeclaredType(*lastType);
        }

        arg->setAttributes(scope, fps.attributes);
        arg->setSyntax(decl);

        if (!decl.dimensions.empty())
            arg->getDeclaredType()->setDimensionSyntax(decl.dimensions);

        if (decl.initializer)
            arg->setDefaultValueSyntax(*decl.initializer->expr);

        scope.addMember(*arg);
        arguments.push_back(arg);

        lastDirection = direction;
        lastFlags = flags;
    }

    return resultFlags;
}

bool SubroutineSymbol::hasOutputArgs() const {
    if (!cachedHasOutputArgs.has_value()) {
        cachedHasOutputArgs = false;
        for (auto arg : getArguments()) {
            if (arg->direction != ArgumentDirection::In &&
                (arg->direction != ArgumentDirection::Ref ||
                 !arg->flags.has(VariableFlags::Const))) {
                cachedHasOutputArgs = true;
                break;
            }
        }
    }
    return *cachedHasOutputArgs;
}

void SubroutineSymbol::connectExternInterfacePrototype() const {
    if (prototype)
        return;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    SLANG_ASSERT(scope && syntax);

    auto nameToken = syntax->as<FunctionDeclarationSyntax>().prototype->name->getFirstToken();
    auto ifaceName = nameToken.valueText();
    auto symbol = scope->find(ifaceName);
    if (!symbol) {
        if (!ifaceName.empty())
            scope->addDiag(diag::UndeclaredIdentifier, nameToken.range()) << ifaceName;
        return;
    }

    const InstanceSymbol* inst = nullptr;
    const ModportSymbol* modport = nullptr;
    if (symbol->kind == SymbolKind::InterfacePort) {
        const Symbol* conn;
        auto& port = symbol->as<InterfacePortSymbol>();
        std::tie(conn, modport) = port.getConnection();
        if (!conn)
            return;

        if (conn->kind == SymbolKind::InstanceArray) {
            scope->addDiag(diag::ExternIfaceArrayMethod, nameToken.range());
            return;
        }

        inst = &conn->as<InstanceSymbol>();
    }
    else if (symbol->kind == SymbolKind::Instance) {
        inst = &symbol->as<InstanceSymbol>();
        if (!inst->isInterface()) {
            scope->addDiag(diag::NotAnInterfaceOrPort, nameToken.range()) << ifaceName;
            return;
        }
    }
    else if (symbol->kind == SymbolKind::InstanceArray) {
        scope->addDiag(diag::ExternIfaceArrayMethod, nameToken.range());
        return;
    }
    else {
        if (symbol->kind != SymbolKind::UninstantiatedDef)
            scope->addDiag(diag::NotAnInterfaceOrPort, nameToken.range()) << ifaceName;
        return;
    }

    auto ifaceMethod = inst->body.find(name);
    if (!ifaceMethod) {
        if (!name.empty())
            scope->addDiag(diag::UnknownMember, location) << name << ifaceName;
        return;
    }

    if (ifaceMethod->kind != SymbolKind::Subroutine) {
        auto& diag = scope->addDiag(diag::NotASubroutine, location);
        diag << name;
        diag.addNote(diag::NoteDeclarationHere, ifaceMethod->location);
        return;
    }

    auto& sub = ifaceMethod->as<SubroutineSymbol>();
    if (!sub.flags.has(MethodFlags::InterfaceExtern)) {
        auto& diag = scope->addDiag(diag::IfaceMethodNotExtern, location);
        diag << name;
        diag.addNote(diag::NoteDeclarationHere, ifaceMethod->location);
        return;
    }

    auto proto = sub.getPrototype();
    SLANG_ASSERT(proto);

    if (!proto->flags.has(MethodFlags::ForkJoin) && proto->getFirstExternImpl() != nullptr) {
        auto& diag = scope->addDiag(diag::DupInterfaceExternMethod, location);
        diag << (subroutineKind == SubroutineKind::Function ? "function"sv : "task"sv);
        diag << ifaceName << name;
        diag.addNote(diag::NotePreviousDefinition, proto->getFirstExternImpl()->impl->location);
    }

    proto->addExternImpl(*this);
    proto->checkMethodMatch(*scope, *this);
    prototype = proto;

    // If our connection goes through a modport that exports us we should register ourselves
    // as an implementation for that export to facilitate checking for missing exports later.
    if (modport && modport->hasExports) {
        if (auto it = modport->getNameMap().find(name); it != modport->getNameMap().end()) {
            if (it->second && it->second->kind == SymbolKind::MethodPrototype) {
                auto& modportProto = it->second->as<MethodPrototypeSymbol>();
                if (modportProto.flags.has(MethodFlags::ModportExport))
                    modportProto.addExternImpl(*this);
            }
        }
    }
}

static std::string flagsToStr(bitmask<MethodFlags> flags) {
    std::string str;
    if (flags.has(MethodFlags::Virtual))
        str += "virtual,";
    if (flags.has(MethodFlags::Pure))
        str += "pure,";
    if (flags.has(MethodFlags::Static))
        str += "static,";
    if (flags.has(MethodFlags::Constructor))
        str += "ctor,";
    if (flags.has(MethodFlags::InterfaceExtern))
        str += "ifaceExtern,";
    if (flags.has(MethodFlags::ModportImport))
        str += "modportImport,";
    if (flags.has(MethodFlags::ModportExport))
        str += "modportExport,";
    if (flags.has(MethodFlags::DPIImport))
        str += "dpi,";
    if (flags.has(MethodFlags::DPIContext))
        str += "context,";
    if (flags.has(MethodFlags::ForkJoin))
        str += "forkJoin,";
    if (flags.has(MethodFlags::DefaultedSuperArg))
        str += "defaultedSuperArg,";
    if (flags.has(MethodFlags::Initial))
        str += "initial,";
    if (flags.has(MethodFlags::Extends))
        str += "extends,";
    if (flags.has(MethodFlags::Final))
        str += "final,";
    if (!str.empty())
        str.pop_back();
    return str;
}

void SubroutineSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("returnType", getReturnType());
    serializer.write("defaultLifetime", toString(defaultLifetime));
    serializer.write("subroutineKind", toString(subroutineKind));
    serializer.write("body", getBody());
    serializer.write("visibility", toString(visibility));

    serializer.startArray("arguments");
    for (auto arg : arguments)
        serializer.serialize(*arg);
    serializer.endArray();

    if (flags)
        serializer.write("flags", flagsToStr(flags));
}

void SubroutineSymbol::addThisVar(const Type& type) {
    auto tv = getCompilation().emplace<VariableSymbol>("this", type.location,
                                                       VariableLifetime::Automatic);
    tv->setType(type);
    tv->flags |= VariableFlags::Const | VariableFlags::CompilerGenerated;
    thisVar = tv;
    addMember(*thisVar);
}

MethodPrototypeSymbol::MethodPrototypeSymbol(Compilation& compilation, std::string_view name,
                                             SourceLocation loc, SubroutineKind subroutineKind,
                                             Visibility visibility, bitmask<MethodFlags> flags) :
    Symbol(SymbolKind::MethodPrototype, name, loc), Scope(compilation, this),
    declaredReturnType(*this), subroutineKind(subroutineKind), visibility(visibility),
    flags(flags) {
}

MethodPrototypeSymbol& MethodPrototypeSymbol::fromSyntax(const Scope& scope,
                                                         const ClassMethodPrototypeSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto& proto = *syntax.prototype;
    auto [flags, visibility] = getMethodFlags(syntax.qualifiers, proto);
    auto subroutineKind = proto.keyword.kind == TokenKind::TaskKeyword ? SubroutineKind::Task
                                                                       : SubroutineKind::Function;

    Token nameToken = proto.name->getLastToken();
    if (nameToken.kind == TokenKind::NewKeyword)
        flags |= MethodFlags::Constructor;

    auto result = comp.emplace<MethodPrototypeSymbol>(comp, nameToken.valueText(),
                                                      nameToken.location(), subroutineKind,
                                                      visibility, flags);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    if (subroutineKind == SubroutineKind::Function && !flags.has(MethodFlags::Constructor))
        result->declaredReturnType.setTypeSyntax(*proto.returnType);
    else
        result->declaredReturnType.setType(comp.getVoidType());

    // Pure virtual methods can only appear in virtual or interface classes.
    if (flags.has(MethodFlags::Pure)) {
        auto& classType = scope.asSymbol().as<ClassType>();
        if (!classType.isAbstract && !classType.isInterface) {
            scope.addDiag(diag::PureInAbstract, nameToken.range());
            flags &= ~MethodFlags::Pure;
        }
    }

    SmallVector<const FormalArgumentSymbol*> arguments;
    if (proto.portList) {
        result->flags |= SubroutineSymbol::buildArguments(*result, scope, *proto.portList,
                                                          VariableLifetime::Automatic, arguments);
    }

    result->arguments = arguments.copy(comp);
    return *result;
}

MethodPrototypeSymbol& MethodPrototypeSymbol::createForModport(const Scope& scope,
                                                               const SyntaxNode& syntax,
                                                               Token nameToken, bool isExport) {
    // Create the prototype symbol.
    auto& comp = scope.getCompilation();
    auto flags = isExport ? MethodFlags::ModportExport : MethodFlags::ModportImport;
    auto name = nameToken.valueText();
    auto result = comp.emplace<MethodPrototypeSymbol>(comp, name, nameToken.location(),
                                                      SubroutineKind::Function, Visibility::Public,
                                                      flags);
    result->setSyntax(syntax);

    // Find the target method we're importing or exporting from the parent interface.
    auto target = scope.find(name);
    if (!target) {
        if (!name.empty()) {
            auto& diag = scope.addDiag(diag::IfaceImportExportTarget, syntax.sourceRange());
            diag << (isExport ? "export"sv : "import"sv);
            diag << name;
        }

        result->subroutine = nullptr;
        result->declaredReturnType.setType(comp.getErrorType());
        return *result;
    }

    if (target->kind == SymbolKind::Subroutine) {
        result->subroutine = &target->as<SubroutineSymbol>();
    }
    else {
        auto& diag = scope.addDiag(diag::NotASubroutine, nameToken.range());
        diag << target->name;
        diag.addNote(diag::NoteDeclarationHere, target->location);

        result->subroutine = nullptr;
        result->declaredReturnType.setType(comp.getErrorType());
    }

    return *result;
}

MethodPrototypeSymbol& MethodPrototypeSymbol::fromSyntax(const Scope& scope,
                                                         const ModportSubroutinePortSyntax& syntax,
                                                         bool isExport) {
    auto& comp = scope.getCompilation();
    auto& proto = *syntax.prototype;
    auto& result = createForModport(scope, syntax, syntax.prototype->name->getLastToken(),
                                    isExport);

    auto target = result.subroutine.value();
    if (!target)
        return result;

    result.subroutineKind = proto.keyword.kind == TokenKind::TaskKeyword ? SubroutineKind::Task
                                                                         : SubroutineKind::Function;

    if (result.subroutineKind == SubroutineKind::Function)
        result.declaredReturnType.setTypeSyntax(*proto.returnType);
    else
        result.declaredReturnType.setType(comp.getVoidType());

    SmallVector<const FormalArgumentSymbol*> arguments;
    if (proto.portList) {
        result.flags |= SubroutineSymbol::buildArguments(result, scope, *proto.portList,
                                                         VariableLifetime::Automatic, arguments);
    }

    result.arguments = arguments.copy(comp);
    result.needsMatchCheck = true;
    return result;
}

MethodPrototypeSymbol& MethodPrototypeSymbol::fromSyntax(const ASTContext& context,
                                                         const ModportNamedPortSyntax& syntax,
                                                         bool isExport) {
    auto& result = createForModport(*context.scope, syntax, syntax.name, isExport);
    auto target = result.subroutine.value();
    if (!target)
        return result;

    result.declaredReturnType.setLink(target->declaredReturnType);
    result.subroutineKind = target->subroutineKind;
    result.arguments = cloneArguments(context.getCompilation(), result, target->getArguments());
    return result;
}

template<typename TSyntax>
MethodPrototypeSymbol& MethodPrototypeSymbol::createExternIfaceMethod(const Scope& scope,
                                                                      const TSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto& proto = *syntax.prototype;
    auto nameToken = proto.name->getLastToken();
    auto subroutineKind = proto.keyword.kind == TokenKind::TaskKeyword ? SubroutineKind::Task
                                                                       : SubroutineKind::Function;

    auto result = comp.emplace<MethodPrototypeSymbol>(comp, nameToken.valueText(),
                                                      nameToken.location(), subroutineKind,
                                                      Visibility::Public,
                                                      MethodFlags::InterfaceExtern);

    result->setSyntax(syntax);

    if (subroutineKind == SubroutineKind::Function)
        result->declaredReturnType.setTypeSyntax(*proto.returnType);
    else
        result->declaredReturnType.setType(comp.getVoidType());

    SmallVector<const FormalArgumentSymbol*> arguments;
    if (proto.portList) {
        result->flags |= SubroutineSymbol::buildArguments(*result, scope, *proto.portList,
                                                          VariableLifetime::Automatic, arguments);
    }

    result->arguments = arguments.copy(comp);
    result->subroutine = &SubroutineSymbol::createFromPrototype(comp, *result, scope);
    return *result;
}

MethodPrototypeSymbol& MethodPrototypeSymbol::fromSyntax(
    const Scope& scope, const ExternInterfaceMethodSyntax& syntax) {

    auto& result = createExternIfaceMethod(scope, syntax);
    if (syntax.forkJoin) {
        if (result.subroutineKind == SubroutineKind::Function)
            scope.addDiag(diag::ExternFuncForkJoin, syntax.forkJoin.range());
        else
            result.flags |= MethodFlags::ForkJoin;
    }

    return result;
}

MethodPrototypeSymbol& MethodPrototypeSymbol::implicitExtern(
    const Scope& scope, const ModportSubroutinePortSyntax& syntax) {

    auto& result = createExternIfaceMethod(scope, syntax);
    return result;
}

const SubroutineSymbol* MethodPrototypeSymbol::getSubroutine() const {
    SLANG_ASSERT(getParentScope() && getParentScope()->asSymbol().getParentScope());

    if (subroutine) {
        if (needsMatchCheck) {
            needsMatchCheck = false;
            if (!checkMethodMatch(*getParentScope(), *subroutine.value()))
                subroutine = nullptr;
        }
        return *subroutine;
    }

    subroutine = nullptr;
    if (name.empty())
        return *subroutine;

    auto& nearScope = *getParentScope();
    auto& parentSym = nearScope.asSymbol();
    auto& outerScope = *parentSym.getParentScope();
    auto& comp = outerScope.getCompilation();

    SLANG_ASSERT(!flags.has(MethodFlags::ModportImport | MethodFlags::ModportExport |
                            MethodFlags::InterfaceExtern));

    // The out-of-block definition must be in our parent scope.
    auto [declSyntax, index, used] = comp.findOutOfBlockDecl(outerScope, parentSym.name, name);
    const FunctionDeclarationSyntax* syntax = nullptr;
    if (declSyntax && (declSyntax->kind == SyntaxKind::FunctionDeclaration ||
                       declSyntax->kind == SyntaxKind::TaskDeclaration)) {
        syntax = &declSyntax->as<FunctionDeclarationSyntax>();
        *used = true;
    }

    if (flags.has(MethodFlags::Pure)) {
        // A pure method should not have a body defined.
        if (syntax) {
            auto& diag = outerScope.addDiag(diag::BodyForPure,
                                            syntax->prototype->name->sourceRange());
            diag.addNote(diag::NoteDeclarationHere, location);
        }
        else {
            // Create a stub subroutine that we can return for callers to reference.
            subroutine = &SubroutineSymbol::createFromPrototype(comp, *this, nearScope);
        }
        return *subroutine;
    }

    // Otherwise, there must be a body for any declared prototype.
    if (!syntax) {
        outerScope.addDiag(diag::NoMemberImplFound, location) << name;
        return nullptr;
    }

    // The method definition must be located after the class definition.
    if (index <= parentSym.getIndex()) {
        auto& diag = outerScope.addDiag(diag::MemberDefinitionBeforeClass,
                                        syntax->prototype->name->getLastToken().location());
        diag << name << parentSym.name;
        diag.addNote(diag::NoteDeclarationHere, parentSym.location);
    }

    subroutine = &SubroutineSymbol::createOutOfBlock(comp, *syntax, *this, nearScope, outerScope,
                                                     index);
    return *subroutine;
}

bool MethodPrototypeSymbol::checkMethodMatch(const Scope& scope,
                                             const SubroutineSymbol& method) const {
    if (method.subroutineKind != subroutineKind) {
        auto& diag = scope.addDiag(diag::MethodKindMismatch, location);
        diag.addNote(diag::NoteDeclarationHere, method.location);
        return false;
    }

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

    auto defArgs = method.getArguments();
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

        // The subroutine itself shouldn't have empty argument names.
        // If it does the parser already errored.
        if (da->name.empty())
            continue;

        if (da->name != pa->name && !pa->name.empty()) {
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

void MethodPrototypeSymbol::addExternImpl(const SubroutineSymbol& impl) const {
    auto node = getCompilation().emplace<ExternImpl>(impl);
    node->next = std::exchange(firstExternImpl, node);
}

void MethodPrototypeSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("returnType", getReturnType());
    serializer.write("subroutineKind", toString(subroutineKind));
    serializer.write("visibility", toString(visibility));

    serializer.startArray("arguments");
    for (auto arg : arguments)
        serializer.serialize(*arg);
    serializer.endArray();

    if (flags)
        serializer.write("flags", flagsToStr(flags));

    if (auto* sub = getSubroutine())
        serializer.write("subroutine", *sub);
}

} // namespace slang::ast
