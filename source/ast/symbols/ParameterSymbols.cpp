//------------------------------------------------------------------------------
// ParameterSymbols.cpp
// Contains parameter-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/ParameterSymbols.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/SpecifySymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

void ParameterSymbolBase::fromLocalSyntax(const Scope& scope,
                                          const ParameterDeclarationStatementSyntax& syntax,
                                          SmallVectorBase<Symbol*>& results) {
    auto paramBase = syntax.parameter;
    if (paramBase->kind == SyntaxKind::ParameterDeclaration) {
        SmallVector<ParameterSymbol*> params;
        ParameterSymbol::fromSyntax(scope, paramBase->as<ParameterDeclarationSyntax>(),
                                    /* isLocal */ true, /* isPort */ false, params);
        for (auto param : params) {
            param->setAttributes(scope, syntax.attributes);
            results.push_back(param);
        }
    }
    else {
        SmallVector<TypeParameterSymbol*> params;
        TypeParameterSymbol::fromSyntax(scope, paramBase->as<TypeParameterDeclarationSyntax>(),
                                        /* isLocal */ true, /* isPort */ false, params);
        for (auto param : params) {
            param->setAttributes(scope, syntax.attributes);
            results.push_back(param);
        }
    }
}

bool ParameterSymbolBase::hasDefault() const {
    if (symbol.kind == SymbolKind::Parameter)
        return symbol.as<ParameterSymbol>().getDeclaredType()->getInitializerSyntax();
    else
        return symbol.as<TypeParameterSymbol>().targetType.getTypeSyntax();
}

ParameterSymbol::ParameterSymbol(std::string_view name, SourceLocation loc, bool isLocal,
                                 bool isPort) :
    ValueSymbol(SymbolKind::Parameter, name, loc,
                DeclaredTypeFlags::InferImplicit | DeclaredTypeFlags::InitializerCantSeeParent |
                    DeclaredTypeFlags::AllowUnboundedLiteral),
    ParameterSymbolBase(*this, isLocal, isPort) {
}

void ParameterSymbol::fromSyntax(const Scope& scope, const ParameterDeclarationSyntax& syntax,
                                 bool isLocal, bool isPort,
                                 SmallVectorBase<ParameterSymbol*>& results) {
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

        results.push_back(param);
    }
}

const ConstantValue& ParameterSymbol::getValue(SourceRange referencingRange) const {
    if (!value) {
        // If no value has been explicitly set, try to set it
        // from our initializer.
        auto init = getInitializer();
        if (init) {
            auto scope = getParentScope();
            SLANG_ASSERT(scope);

            ASTContext ctx(*scope, LookupLocation::max);

            if (evaluating) {
                SLANG_ASSERT(referencingRange.start());

                auto& diag = ctx.addDiag(diag::ConstEvalParamCycle, location) << name;
                diag.addNote(diag::NoteReferencedHere, referencingRange);
                return ConstantValue::Invalid;
            }

            evaluating = true;
            auto guard = ScopeGuard([this] { evaluating = false; });

            value = scope->getCompilation().allocConstant(
                ctx.eval(*init, EvalFlags::AllowUnboundedPlaceholder));

            // If this parameter has an implicit type declared and it was assigned
            // a string literal, make a note so that this parameter gets treated
            // as an implicit string itself in further expressions.
            auto typeSyntax = getDeclaredType()->getTypeSyntax();
            if (typeSyntax && typeSyntax->kind == SyntaxKind::ImplicitType) {
                auto& its = typeSyntax->as<ImplicitTypeSyntax>();
                if (!its.signing && its.dimensions.empty())
                    fromStringLit = init->isImplicitString();
            }
        }
        else {
            value = &ConstantValue::Invalid;
        }
    }
    else if (needsCoercion) {
        auto scope = getParentScope();
        SLANG_ASSERT(scope);

        value = scope->getCompilation().allocConstant(getType().coerceValue(*value));
        needsCoercion = false;
    }

    return *value;
}

bool ParameterSymbol::isImplicitString(SourceRange referencingRange) const {
    if (!value)
        getValue(referencingRange);
    return fromStringLit || value->bad();
}

bool ParameterSymbol::isOverridden() const {
    return getDeclaredType()->getFlags().has(DeclaredTypeFlags::InitializerOverridden);
}

void ParameterSymbol::setValue(Compilation& compilation, ConstantValue newValue,
                               bool newNeedsCoercion) {
    value = compilation.allocConstant(std::move(newValue));
    needsCoercion = newNeedsCoercion;
}

void ParameterSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", getValue());
    serializer.write("isLocal", isLocalParam());
    serializer.write("isPort", isPortParam());
    serializer.write("isBody", isBodyParam());
}

TypeParameterSymbol::TypeParameterSymbol(std::string_view name, SourceLocation loc, bool isLocal,
                                         bool isPort) :
    Symbol(SymbolKind::TypeParameter, name, loc),
    ParameterSymbolBase(*this, isLocal, isPort), targetType(*this) {
}

void TypeParameterSymbol::fromSyntax(const Scope& scope,
                                     const TypeParameterDeclarationSyntax& syntax, bool isLocal,
                                     bool isPort, SmallVectorBase<TypeParameterSymbol*>& results) {
    auto& comp = scope.getCompilation();
    for (auto decl : syntax.declarators) {
        auto name = decl->name.valueText();
        auto loc = decl->name.location();

        auto param = comp.emplace<TypeParameterSymbol>(name, loc, isLocal, isPort);
        param->setSyntax(*decl);

        if (!decl->assignment) {
            param->targetType.setType(comp.getErrorType());
            if (!isPort)
                scope.addDiag(diag::BodyParamNoInitializer, loc);
            else if (isLocal)
                scope.addDiag(diag::LocalParamNoInitializer, loc);
        }
        else {
            param->targetType.setTypeSyntax(*decl->assignment->type);
        }

        results.push_back(param);
    }
}

const Type& TypeParameterSymbol::getTypeAlias() const {
    if (typeAlias)
        return *typeAlias;

    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto alias = scope->getCompilation().emplace<TypeAliasType>(name, location);
    if (auto syntax = getSyntax())
        alias->setSyntax(*syntax);

    alias->targetType.setLink(targetType);
    alias->setParent(*scope, getIndex());

    typeAlias = alias;
    return *typeAlias;
}

bool TypeParameterSymbol::isOverridden() const {
    return getDeclaredType()->getFlags().has(DeclaredTypeFlags::TypeOverridden);
}

void TypeParameterSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("type", targetType.getType());
    serializer.write("isLocal", isLocalParam());
    serializer.write("isPort", isPortParam());
    serializer.write("isBody", isBodyParam());
}

void DefParamSymbol::fromSyntax(const Scope& scope, const DefParamSyntax& syntax,
                                SmallVectorBase<const DefParamSymbol*>& results) {
    auto& comp = scope.getCompilation();
    for (auto assignment : syntax.assignments) {
        auto sym = comp.emplace<DefParamSymbol>(assignment->getFirstToken().location());
        sym->setSyntax(*assignment);
        sym->setAttributes(scope, syntax.attributes);
        results.push_back(sym);
    }
}

const Symbol* DefParamSymbol::getTarget() const {
    if (!initializer)
        resolve();
    return target;
}

const Expression& DefParamSymbol::getInitializer() const {
    if (!initializer)
        resolve();
    return *initializer;
}

const ConstantValue& DefParamSymbol::getValue() const {
    auto v = getInitializer().constant;
    SLANG_ASSERT(v);
    return *v;
}

static const Symbol* checkDefparamHierarchy(const Symbol& target, const Scope& defparamScope) {
    // defparams are not allowed to extend upward through a generate block or instance
    // array and affect a param outside of that hierarchy. To check this, build the parent
    // chain for the target and then walk the defparam's parent chain and see if we pass one
    // of the disallowed nodes before we hit a common ancestor.
    SmallSet<const Scope*, 4> targetChain;
    auto scope = target.getParentScope();
    while (scope) {
        targetChain.emplace(scope);

        auto& sym = scope->asSymbol();
        if (sym.kind == SymbolKind::InstanceBody)
            scope = sym.as<InstanceBodySymbol>().parentInstance->getParentScope();
        else
            scope = sym.getParentScope();
    }

    bool isInsideBind = false;
    scope = &defparamScope;
    do {
        if (auto it = targetChain.find(scope); it != targetChain.end()) {
            // If the defparam is inside a bind instantiation we need
            // to check whether our common ancestor also is.
            if (isInsideBind) {
                auto inst = (*it)->getContainingInstance();
                if (!inst || !inst->isFromBind)
                    return &scope->asSymbol();
            }

            return nullptr;
        }

        auto& sym = scope->asSymbol();
        if (sym.kind == SymbolKind::InstanceArray || sym.kind == SymbolKind::GenerateBlock)
            return &sym;

        if (sym.kind != SymbolKind::InstanceBody) {
            scope = sym.getParentScope();
            continue;
        }

        auto& body = sym.as<InstanceBodySymbol>();
        SLANG_ASSERT(body.parentInstance);
        scope = body.parentInstance->getParentScope();

        isInsideBind |= body.isFromBind;

        // We are also disallowed from having defparams inside an instance that has interface
        // ports that connect to an array from extending outside that hierarchy.
        for (auto conn : body.parentInstance->getPortConnections()) {
            if (auto connSym = conn->getIfaceInstance()) {
                if (connSym->kind == SymbolKind::Modport) {
                    auto parent = connSym->getParentScope();
                    SLANG_ASSERT(parent);
                    connSym = &parent->asSymbol();
                }

                if (connSym->kind == SymbolKind::InstanceBody) {
                    auto& connBody = connSym->as<InstanceBodySymbol>();
                    SLANG_ASSERT(connBody.parentInstance);
                    connSym = connBody.parentInstance;
                }

                if (connSym->kind == SymbolKind::InstanceArray ||
                    (connSym->getParentScope() &&
                     connSym->getParentScope()->asSymbol().kind == SymbolKind::InstanceArray)) {
                    return body.parentInstance;
                }
            }
        }
    } while (scope);

    return nullptr;
}

void DefParamSymbol::resolve() const {
    auto syntax = getSyntax();
    auto scope = getParentScope();
    SLANG_ASSERT(syntax && scope);

    auto& comp = scope->getCompilation();
    auto& assignment = syntax->as<DefParamAssignmentSyntax>();

    ASTContext context(*scope, LookupLocation::before(*this));
    LookupResult result;
    Lookup::name(*assignment.name, context, LookupFlags::NoSelectors, result);
    result.reportDiags(context);

    target = result.found;
    if (target && target->kind != SymbolKind::Parameter) {
        auto& diag = context.addDiag(diag::DefParamTarget, assignment.name->sourceRange());
        diag.addNote(diag::NoteDeclarationHere, target->location);
        target = nullptr;
    }

    auto makeInvalid = [&] {
        initializer = comp.emplace<InvalidExpression>(nullptr, comp.getErrorType());
        initializer->constant = &ConstantValue::Invalid;
    };

    if (!target) {
        makeInvalid();
        return;
    }

    auto& param = target->as<ParameterSymbol>();
    if (param.isLocalParam()) {
        context.addDiag(diag::DefParamLocal, assignment.name->sourceRange()) << param.name;
        makeInvalid();
        return;
    }

    if (auto invalidParent = checkDefparamHierarchy(*target, *scope)) {
        auto& diag = context.addDiag(diag::DefparamBadHierarchy, assignment.name->sourceRange());
        diag.addNote(diag::NoteCommonAncestor, invalidParent->location);

        makeInvalid();
        return;
    }

    // We need to know the parameter's type (or lack thereof) in order to
    // correctly bind a value for it.
    auto& exprSyntax = *assignment.setter->expr;
    auto equalsLoc = assignment.setter->equals.location();
    auto declType = param.getDeclaredType();
    auto typeSyntax = declType->getTypeSyntax();

    if (typeSyntax && typeSyntax->kind == SyntaxKind::ImplicitType) {
        ASTContext typeContext(*param.getParentScope(), LookupLocation::before(param));
        auto [expr, type] = Expression::bindImplicitParam(*typeSyntax, exprSyntax, equalsLoc,
                                                          context, typeContext);
        initializer = expr;
    }
    else {
        initializer = &Expression::bindRValue(declType->getType(), exprSyntax, equalsLoc, context);
    }

    context.eval(*initializer);
    if (!initializer->constant)
        initializer->constant = &ConstantValue::Invalid;
}

void DefParamSymbol::serializeTo(ASTSerializer& serializer) const {
    if (auto t = getTarget())
        serializer.writeLink("target", *t);
    serializer.write("value", getValue());
}

SpecparamSymbol::SpecparamSymbol(std::string_view name, SourceLocation loc) :
    ValueSymbol(SymbolKind::Specparam, name, loc,
                DeclaredTypeFlags::InferImplicit | DeclaredTypeFlags::InitializerCantSeeParent) {
}

const ConstantValue& SpecparamSymbol::getValue(SourceRange referencingRange) const {
    if (!value1) {
        // If no value has been explicitly set, try to set it
        // from our initializer.
        auto init = getInitializer();
        if (init) {
            auto scope = getParentScope();
            SLANG_ASSERT(scope);

            ASTContext ctx(*scope, LookupLocation::before(*this));

            if (evaluating) {
                SLANG_ASSERT(referencingRange.start());

                auto& diag = ctx.addDiag(diag::ConstEvalParamCycle, location) << name;
                diag.addNote(diag::NoteReferencedHere, referencingRange);
                return ConstantValue::Invalid;
            }

            evaluating = true;
            auto guard = ScopeGuard([this] { evaluating = false; });

            auto& comp = scope->getCompilation();
            value1 = comp.allocConstant(ctx.eval(*init, EvalFlags::SpecparamsAllowed));

            // Specparams can also be a "PATHPULSE$" which has two values to bind.
            auto syntax = getSyntax();
            SLANG_ASSERT(syntax);

            auto& decl = syntax->as<SpecparamDeclaratorSyntax>();
            if (auto exprSyntax = decl.value2) {
                auto& expr2 = Expression::bindRValue(getType(), *exprSyntax, decl.equals.location(),
                                                     ctx);
                value2 = comp.allocConstant(ctx.eval(expr2, EvalFlags::SpecparamsAllowed));
            }
            else {
                value2 = &ConstantValue::Invalid;
            }
        }
        else {
            value1 = &ConstantValue::Invalid;
            value2 = &ConstantValue::Invalid;
        }
    }
    return *value1;
}

const ConstantValue& SpecparamSymbol::getPulseRejectLimit() const {
    SLANG_ASSERT(isPathPulse);
    getValue();
    return *value1;
}

const ConstantValue& SpecparamSymbol::getPulseErrorLimit() const {
    SLANG_ASSERT(isPathPulse);
    getValue();
    return *value2;
}

void SpecparamSymbol::fromSyntax(const Scope& scope, const SpecparamDeclarationSyntax& syntax,
                                 SmallVectorBase<const SpecparamSymbol*>& results) {
    for (auto decl : syntax.declarators) {
        auto loc = decl->name.location();
        auto param = scope.getCompilation().emplace<SpecparamSymbol>(decl->name.valueText(), loc);
        param->setSyntax(*decl);
        param->setDeclaredType(*syntax.type);
        param->setInitializerSyntax(*decl->value1, decl->equals.location());
        param->setAttributes(scope, syntax.attributes);
        results.push_back(param);

        if (decl->value2)
            param->isPathPulse = true;
    }
}

void SpecparamSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("isPathPulse", isPathPulse);
    if (isPathPulse) {
        serializer.write("rejectLimit", getPulseRejectLimit());
        serializer.write("errorLimit", getPulseErrorLimit());
        if (auto symbol = getPathSource())
            serializer.writeLink("pathSource", *symbol);
        if (auto symbol = getPathDest())
            serializer.writeLink("pathDest", *symbol);
    }
    else {
        serializer.write("value", getValue());
    }
}

void SpecparamSymbol::resolvePathPulse() const {
    pathPulseResolved = true;
    if (!isPathPulse)
        return;

    auto parent = getParentScope();
    SLANG_ASSERT(parent);

    auto prefix = "PATHPULSE$"sv;
    if (name.starts_with(prefix) && parent->asSymbol().kind == SymbolKind::SpecifyBlock) {
        auto path = name.substr(prefix.length());
        if (!path.empty()) {
            auto loc = location + prefix.length();
            auto nameError = [&] {
                parent->addDiag(diag::PathPulseInvalidPathName,
                                SourceRange{loc, loc + path.length()})
                    << path;
            };

            auto index = path.find('$');
            if (index == std::string_view::npos) {
                nameError();
                return;
            }

            auto source = path.substr(0, index);
            auto dest = path.substr(index + 1);
            if (source.empty() || dest.empty()) {
                nameError();
                return;
            }

            pathSource = resolvePathTerminal(source, *parent, loc,
                                             /* isSource */ true);
            pathDest = resolvePathTerminal(dest, *parent, loc + source.length(),
                                           /* isSource */ false);
        }
    }
}

const Symbol* SpecparamSymbol::resolvePathTerminal(std::string_view terminalName,
                                                   const Scope& parent, SourceLocation loc,
                                                   bool isSource) const {
    auto parentParent = parent.asSymbol().getParentScope();
    SLANG_ASSERT(parentParent);

    SourceRange sourceRange{loc, loc + terminalName.length()};
    auto symbol = Lookup::unqualifiedAt(*parentParent, terminalName,
                                        LookupLocation::after(parent.asSymbol()), sourceRange,
                                        LookupFlags::NoParentScope);
    if (!symbol)
        return nullptr;

    if (!symbol->isValue()) {
        auto code = isSource ? diag::InvalidSpecifySource : diag::InvalidSpecifyDest;
        auto& diag = parent.addDiag(code, sourceRange) << terminalName;
        diag.addNote(diag::NoteDeclarationHere, symbol->location);
        return nullptr;
    }

    auto& value = symbol->as<ValueSymbol>();
    if (!SpecifyBlockSymbol::checkPathTerminal(value, value.getType(), *parentParent, isSource,
                                               /* allowAnyNet */ false, sourceRange)) {
        return nullptr;
    }

    return symbol;
}

} // namespace slang::ast
