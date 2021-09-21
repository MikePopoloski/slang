//------------------------------------------------------------------------------
// VariableSymbols.cpp
// Contains variable-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/VariableSymbols.h"

#include "slang/binding/BindContext.h"
#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/BlockSymbols.h"
#include "slang/symbols/PortSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/types/NetType.h"
#include "slang/types/Type.h"

namespace slang {

static string_view getPotentialNetTypeName(const DataTypeSyntax& syntax) {
    if (syntax.kind == SyntaxKind::NamedType) {
        auto& namedType = syntax.as<NamedTypeSyntax>();
        if (namedType.name->kind == SyntaxKind::IdentifierName)
            return namedType.name->as<IdentifierNameSyntax>().identifier.valueText();

        if (namedType.name->kind == SyntaxKind::ClassName)
            return namedType.name->as<ClassNameSyntax>().identifier.valueText();
    }
    return "";
}

static VariableLifetime getDefaultLifetime(const Scope& scope) {
    const Symbol& sym = scope.asSymbol();
    switch (sym.kind) {
        case SymbolKind::StatementBlock:
            return sym.as<StatementBlockSymbol>().defaultLifetime;
        case SymbolKind::Subroutine:
            return sym.as<SubroutineSymbol>().defaultLifetime;
        case SymbolKind::MethodPrototype:
            return VariableLifetime::Automatic;
        default:
            return VariableLifetime::Static;
    }
}

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                const Scope& scope, SmallVector<const ValueSymbol*>& results) {
    // This might actually be a net declaration with a user defined net type. That can only
    // be true if the data type syntax is a simple identifier or a "class name",
    // so if we see that it is, perform a lookup and see what comes back.
    if (syntax.modifiers.empty()) {
        string_view simpleName = getPotentialNetTypeName(*syntax.type);
        if (!simpleName.empty()) {
            auto result = Lookup::unqualified(scope, simpleName);
            if (result && result->kind == SymbolKind::NetType) {
                const NetType& netType = result->as<NetType>();
                netType.getAliasTarget(); // force resolution of target

                auto& declaredType = *netType.getDeclaredType();
                for (auto declarator : syntax.declarators) {
                    auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                              declarator->name.location(), netType);
                    net->getDeclaredType()->copyTypeFrom(declaredType);
                    net->setFromDeclarator(*declarator);
                    net->setAttributes(scope, syntax.attributes);
                    results.append(net);
                }
                return;
            }
        }
    }

    bool isConst = false;
    bool inProceduralContext = scope.isProceduralContext();
    optional<VariableLifetime> lifetime;
    for (Token mod : syntax.modifiers) {
        switch (mod.kind) {
            case TokenKind::VarKeyword:
                break;
            case TokenKind::ConstKeyword:
                isConst = true;
                break;
            case TokenKind::StaticKeyword:
                // Static lifetimes are allowed in all contexts.
                lifetime = VariableLifetime::Static;
                break;
            case TokenKind::AutomaticKeyword:
                // Automatic lifetimes are only allowed in procedural contexts.
                lifetime = VariableLifetime::Automatic;
                if (!inProceduralContext) {
                    scope.addDiag(diag::AutomaticNotAllowed, mod.range());
                    lifetime = VariableLifetime::Static;
                }
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    // If no explicit lifetime is provided, find the default one for this scope.
    bool hasExplicitLifetime = lifetime.has_value();
    if (!hasExplicitLifetime)
        lifetime = getDefaultLifetime(scope);

    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location(), *lifetime);
        variable->isConstant = isConst;
        variable->setDeclaredType(*syntax.type);
        variable->setFromDeclarator(*declarator);
        variable->setAttributes(scope, syntax.attributes);
        results.append(variable);

        // If this is a static variable in a procedural context and it has an initializer,
        // the spec requires that the static keyword must be explicitly provided.
        if (*lifetime == VariableLifetime::Static && !hasExplicitLifetime &&
            declarator->initializer && scope.isProceduralContext()) {
            scope.addDiag(diag::StaticInitializerMustBeExplicit, declarator->name.range());
        }

        // Constants require an initializer.
        if (isConst && !declarator->initializer)
            scope.addDiag(diag::ConstVarNoInitializer, declarator->name.range());
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax,
                                           const VariableSymbol* lastVar) {
    auto nameToken = syntax.declarator->name;
    auto var = compilation.emplace<VariableSymbol>(nameToken.valueText(), nameToken.location(),
                                                   VariableLifetime::Automatic);

    if (syntax.type)
        var->setDeclaredType(*syntax.type);
    else {
        ASSERT(lastVar);
        var->getDeclaredType()->copyTypeFrom(*lastVar->getDeclaredType());
    }

    var->setFromDeclarator(*syntax.declarator);
    return *var;
}

VariableSymbol::VariableSymbol(string_view name, SourceLocation loc, VariableLifetime lifetime) :
    VariableSymbol(SymbolKind::Variable, name, loc, lifetime) {
}

VariableSymbol::VariableSymbol(SymbolKind childKind, string_view name, SourceLocation loc,
                               VariableLifetime lifetime) :
    ValueSymbol(childKind, name, loc),
    lifetime(lifetime) {
    if (lifetime == VariableLifetime::Automatic)
        getDeclaredType()->addFlags(DeclaredTypeFlags::AutomaticInitializer);
}

void VariableSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("lifetime", toString(lifetime));
    serializer.write("isConstant", isConstant);
    serializer.write("isCompilerGenerated", isCompilerGenerated);
}

FormalArgumentSymbol::FormalArgumentSymbol(string_view name, SourceLocation loc,
                                           ArgumentDirection direction, VariableLifetime lifetime) :
    VariableSymbol(SymbolKind::FormalArgument, name, loc, lifetime),
    direction(direction) {
}

void FormalArgumentSymbol::fromSyntax(const Scope& scope, const PortDeclarationSyntax& syntax,
                                      SmallVector<const FormalArgumentSymbol*>& results) {
    if (syntax.header->kind != SyntaxKind::VariablePortHeader) {
        scope.addDiag(diag::ExpectedFunctionPort, syntax.header->sourceRange());
        return;
    }

    auto& comp = scope.getCompilation();
    auto& header = syntax.header->as<VariablePortHeaderSyntax>();
    ArgumentDirection direction = SemanticFacts::getDirection(header.direction.kind);
    VariableLifetime lifetime = getDefaultLifetime(scope);

    bool isConst = false;
    if (header.constKeyword) {
        ASSERT(direction == ArgumentDirection::Ref);
        isConst = true;
    }

    for (auto declarator : syntax.declarators) {
        auto arg = comp.emplace<FormalArgumentSymbol>(
            declarator->name.valueText(), declarator->name.location(), direction, lifetime);
        arg->isConstant = isConst;
        arg->setDeclaredType(*header.dataType);
        arg->setFromDeclarator(*declarator);
        arg->setAttributes(scope, syntax.attributes);
        results.append(arg);
    }
}

bool FormalArgumentSymbol::mergeVariable(const VariableSymbol& variable) {
    // If we've already merged one variable already, we can't do any more.
    if (mergedVar)
        return false;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    ASSERT(scope && syntax && syntax->parent);
    if (syntax->parent->kind != SyntaxKind::PortDeclaration)
        return false;

    auto& portDecl = syntax->parent->as<PortDeclarationSyntax>();
    auto& header = portDecl.header->as<VariablePortHeaderSyntax>();

    // If the port has a type declared this is already a full definition and
    // we shouldn't merge with any other variables (the caller will error for us).
    if (header.varKeyword || header.dataType->kind != SyntaxKind::ImplicitType)
        return false;

    // Save this variable reference; our DeclaredType will look into it later
    // when our type is fully resolved to merge in the variable's type info.
    getDeclaredType()->addFlags(DeclaredTypeFlags::FormalArgMergeVar);
    mergedVar = &variable;
    return true;
}

void FormalArgumentSymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("direction", toString(direction));
}

void FieldSymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("offset", offset);
}

void NetSymbol::fromSyntax(const Scope& scope, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {
    auto& comp = scope.getCompilation();
    const NetType& netType = comp.getNetType(syntax.netType.kind);

    ExpansionHint expansionHint = ExpansionHint::None;
    switch (syntax.expansionHint.kind) {
        case TokenKind::VectoredKeyword:
            expansionHint = ExpansionHint::Vectored;
            break;
        case TokenKind::ScalaredKeyword:
            expansionHint = ExpansionHint::Scalared;
            break;
        default:
            break;
    }

    for (auto declarator : syntax.declarators) {
        auto net = comp.emplace<NetSymbol>(declarator->name.valueText(),
                                           declarator->name.location(), netType);
        net->expansionHint = expansionHint;
        net->setDeclaredType(*syntax.type, declarator->dimensions);
        net->setFromDeclarator(*declarator);
        net->setAttributes(scope, syntax.attributes);
        results.append(net);
    }
}

void NetSymbol::fromSyntax(const BindContext& context,
                           const UserDefinedNetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {
    auto& comp = context.getCompilation();

    const NetType* netType;
    auto result = Lookup::unqualifiedAt(*context.scope, syntax.netType.valueText(),
                                        context.getLocation(), syntax.netType.range());

    if (result && result->kind != SymbolKind::NetType) {
        context.addDiag(diag::VarDeclWithDelay, syntax.delay->sourceRange());
        result = nullptr;
    }

    if (!result)
        netType = &comp.getNetType(TokenKind::Unknown);
    else
        netType = &result->as<NetType>();

    netType->getAliasTarget(); // force resolution of target
    auto& declaredType = *netType->getDeclaredType();

    for (auto declarator : syntax.declarators) {
        auto net = comp.emplace<NetSymbol>(declarator->name.valueText(),
                                           declarator->name.location(), *netType);
        net->getDeclaredType()->copyTypeFrom(declaredType);
        net->setFromDeclarator(*declarator);
        net->setAttributes(*context.scope, syntax.attributes);
        results.append(net);
    }
}

const TimingControl* NetSymbol::getDelay() const {
    if (delay)
        return *delay;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    if (!scope || !syntax || !syntax->parent) {
        delay = nullptr;
        return nullptr;
    }

    BindContext context(*scope, LookupLocation::before(*this), BindFlags::NonProcedural);

    auto& parent = *syntax->parent;
    if (parent.kind == SyntaxKind::NetDeclaration) {
        auto delaySyntax = parent.as<NetDeclarationSyntax>().delay;
        if (delaySyntax) {
            delay = &TimingControl::bind(*delaySyntax, context);
            return *delay;
        }
    }
    else if (parent.kind == SyntaxKind::DataDeclaration) {
        auto type = parent.as<DataDeclarationSyntax>().type;
        if (type->kind == SyntaxKind::NamedType) {
            auto& nt = type->as<NamedTypeSyntax>();
            if (nt.name->kind == SyntaxKind::ClassName) {
                auto params = nt.name->as<ClassNameSyntax>().parameters;
                delay = &DelayControl::fromParams(scope->getCompilation(), *params, context);
                return *delay;
            }
        }
    }

    delay = nullptr;
    return nullptr;
}

void NetSymbol::checkInitializer() const {
    // Disallow initializers inside packages. Enforcing this check requires knowing
    // about user-defined nettypes, which is why we can't just do it in the parser.
    auto init = getInitializer();
    auto parent = getParentScope();
    if (init && parent && parent->asSymbol().kind == SymbolKind::Package && !init->bad())
        parent->addDiag(diag::PackageNetInit, init->sourceRange);
}

void NetSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("netType", netType);

    switch (expansionHint) {
        case Vectored:
            serializer.write("expansionHint", "vectored"sv);
            break;
        case Scalared:
            serializer.write("expansionHint", "scalared"sv);
            break;
        default:
            break;
    }

    if (auto delayCtrl = getDelay())
        serializer.write("delay", *delayCtrl);
}

IteratorSymbol::IteratorSymbol(const Scope& scope, string_view name, SourceLocation loc,
                               const Type& arrayType) :
    VariableSymbol(SymbolKind::Iterator, name, loc, VariableLifetime::Automatic),
    arrayType(arrayType) {

    isConstant = true;
    setParent(scope);

    const Type* elemType = arrayType.getArrayElementType();
    if (!elemType)
        elemType = &scope.getCompilation().getErrorType();

    setType(*elemType);
}

IteratorSymbol::IteratorSymbol(string_view name, SourceLocation loc, const Type& arrayType,
                               const Type& indexType) :
    VariableSymbol(SymbolKind::Iterator, name, loc, VariableLifetime::Automatic),
    arrayType(arrayType) {

    isConstant = true;
    setType(indexType);
}

ClockVarSymbol::ClockVarSymbol(string_view name, SourceLocation loc, ArgumentDirection direction,
                               ClockingSkew inputSkew, ClockingSkew outputSkew) :
    VariableSymbol(SymbolKind::ClockVar, name, loc, VariableLifetime::Static),
    direction(direction), inputSkew(inputSkew), outputSkew(outputSkew) {
}

void ClockVarSymbol::fromSyntax(const Scope& scope, const ClockingItemSyntax& syntax,
                                SmallVector<const ClockVarSymbol*>& results) {
    // Lookups should happen in the parent of the clocking block, since other
    // clocking block members cannot reference each other.
    auto& comp = scope.getCompilation();
    auto parent = scope.asSymbol().getParentScope();
    ASSERT(parent);

    LookupLocation ll = LookupLocation::before(scope.asSymbol());
    BindContext context(*parent, ll);

    ArgumentDirection dir = ArgumentDirection::In;
    ClockingSkew inputSkew, outputSkew;
    if (syntax.direction->input.kind == TokenKind::InOutKeyword) {
        dir = ArgumentDirection::InOut;
    }
    else {
        if (syntax.direction->input) {
            if (syntax.direction->inputSkew)
                inputSkew = ClockingSkew::fromSyntax(*syntax.direction->inputSkew, context);
        }

        if (syntax.direction->output) {
            dir = syntax.direction->input ? ArgumentDirection::InOut : ArgumentDirection::Out;
            if (syntax.direction->outputSkew)
                outputSkew = ClockingSkew::fromSyntax(*syntax.direction->outputSkew, context);
        }
    }

    for (auto decl : syntax.decls) {
        auto name = decl->name;
        auto arg = comp.emplace<ClockVarSymbol>(name.valueText(), name.location(), dir, inputSkew,
                                                outputSkew);
        arg->setSyntax(*decl);
        arg->setAttributes(*parent, syntax.attributes);
        results.append(arg);

        // If there is an initializer expression we take our type from that.
        // Otherwise we need to lookup the signal in our parent scope and
        // take the type from that.
        if (decl->value) {
            auto& expr = Expression::bind(*decl->value->expr, context, BindFlags::NonProcedural);
            arg->setType(*expr.type);
            arg->setInitializer(expr);

            if (dir != ArgumentDirection::In)
                expr.verifyAssignable(context, decl->value->equals.location());
        }
        else {
            auto sym = Lookup::unqualifiedAt(*parent, name.valueText(), ll, name.range());
            if (sym && sym->kind != SymbolKind::Net && sym->kind != SymbolKind::Variable) {
                auto& diag = context.addDiag(diag::InvalidClockingSignal, name.range());
                diag << name.valueText();
                diag.addNote(diag::NoteDeclarationHere, sym->location);
                sym = nullptr;
            }

            if (sym) {
                auto sourceType = sym->getDeclaredType();
                ASSERT(sourceType);
                arg->getDeclaredType()->copyTypeFrom(*sourceType);
            }
        }
    }
}

void ClockVarSymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);

    serializer.write("direction", toString(direction));

    if (inputSkew.hasValue()) {
        serializer.writeProperty("inputSkew");
        serializer.startObject();
        inputSkew.serializeTo(serializer);
        serializer.endObject();
    }

    if (outputSkew.hasValue()) {
        serializer.writeProperty("outputSkew");
        serializer.startObject();
        outputSkew.serializeTo(serializer);
        serializer.endObject();
    }
}

LocalAssertionVarSymbol::LocalAssertionVarSymbol(string_view name, SourceLocation loc) :
    VariableSymbol(SymbolKind::LocalAssertionVar, name, loc, VariableLifetime::Automatic) {
    getDeclaredType()->addFlags(DeclaredTypeFlags::RequireSequenceType);
}

void LocalAssertionVarSymbol::fromSyntax(const Scope& scope,
                                         const LocalVariableDeclarationSyntax& syntax,
                                         SmallVector<const LocalAssertionVarSymbol*>& results) {
    auto& comp = scope.getCompilation();
    for (auto declarator : syntax.declarators) {
        auto var = comp.emplace<LocalAssertionVarSymbol>(declarator->name.valueText(),
                                                         declarator->name.location());
        var->setDeclaredType(*syntax.type);
        var->setFromDeclarator(*declarator);
        var->setAttributes(scope, syntax.attributes);
        results.append(var);

        // Local variables don't get added to any scope as members but
        // we still need a parent pointer set so they can participate in lookups.
        var->setParent(scope);
    }
}

} // namespace slang
