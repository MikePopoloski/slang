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
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/SpecifySymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/ScopeGuard.h"

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

void ParameterSymbolBase::checkDefaultExpression() const {
    // A visitor that finds all Name expressions and
    // performs a lookup to ensure that they resolve.
    struct Visitor : public SyntaxVisitor<Visitor> {
        explicit Visitor(const ASTContext& context) : context(context) {}

        void handle(const NameSyntax& syntax) {
            LookupResult result;
            Lookup::name(syntax, context, LookupFlags::ForceHierarchical, result);
            result.reportDiags(context);
            if (result.found)
                context.getCompilation().noteReference(*result.found);

            for (auto& selector : result.selectors) {
                if (auto elemSel = std::get_if<0>(&selector))
                    (*elemSel)->visit(*this);
            }
        }

        void handle(const AssignmentPatternItemSyntax& syntax) {
            // Avoid visiting the key which can name a struct member
            // and so should not be looked up.
            syntax.expr->visit(*this);
        }

        const ASTContext& context;
    };

    if (defaultValSyntax) {
        // We can't properly bind this default expression because it may
        // rely on other parameters that have been overridden in conflicting
        // ways, so the best we can do is resolve names and mark them used.
        auto scope = symbol.getParentScope();
        SLANG_ASSERT(scope);

        ASTContext context(*scope, LookupLocation::before(symbol));
        Visitor visitor(context);
        defaultValSyntax->visit(visitor);
    }
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
        auto scope = getParentScope();
        SLANG_ASSERT(scope);

        ASTContext ctx(*scope, LookupLocation::max);
        if (isFromConf)
            ctx.flags |= ASTFlags::ConfigParam;

        if (evaluating) {
            SLANG_ASSERT(referencingRange.start());

            auto& diag = ctx.addDiag(diag::ConstEvalParamCycle, location) << name;
            diag.addNote(diag::NoteReferencedHere, referencingRange);
            return ConstantValue::Invalid;
        }

        evaluating = true;
        auto guard = ScopeGuard([this] { evaluating = false; });

        // If no value has been explicitly set, try to set it
        // from our initializer.
        auto init = getInitializer();
        if (init) {
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
    if (!value) {
        getValue(referencingRange);
        SLANG_ASSERT(value);
    }
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

static DeclaredTypeFlags getTypeParamFlags(const Scope& scope) {
    // v1800-2023: Type parameter assignments are allowed to reference
    // incomplete forward class types now.
    if (scope.getCompilation().languageVersion() >= LanguageVersion::v1800_2023)
        return DeclaredTypeFlags::TypedefTarget;
    return DeclaredTypeFlags::None;
}

TypeParameterSymbol::TypeParameterSymbol(const Scope& scope, std::string_view name,
                                         SourceLocation loc, bool isLocal, bool isPort,
                                         ForwardTypeRestriction typeRestriction) :
    Symbol(SymbolKind::TypeParameter, name, loc), ParameterSymbolBase(*this, isLocal, isPort),
    targetType(*this, getTypeParamFlags(scope)), typeRestriction(typeRestriction) {

    auto alias = scope.getCompilation().emplace<TypeAliasType>(name, loc);
    alias->setParent(scope);
    alias->targetType.setLink(targetType);
    typeAlias = alias;
}

void TypeParameterSymbol::fromSyntax(const Scope& scope,
                                     const TypeParameterDeclarationSyntax& syntax, bool isLocal,
                                     bool isPort, SmallVectorBase<TypeParameterSymbol*>& results) {
    auto& comp = scope.getCompilation();
    auto typeRestriction = ForwardTypeRestriction::None;
    if (syntax.typeRestriction)
        typeRestriction = SemanticFacts::getTypeRestriction(*syntax.typeRestriction);

    for (auto decl : syntax.declarators) {
        auto name = decl->name.valueText();
        auto loc = decl->name.location();

        auto param = comp.emplace<TypeParameterSymbol>(scope, name, loc, isLocal, isPort,
                                                       typeRestriction);
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

void TypeParameterSymbol::checkTypeRestriction() const {
    if (typeRestriction != ForwardTypeRestriction::None) {
        auto& type = targetType.getType();
        if (!type.isError() && typeRestriction != SemanticFacts::getTypeRestriction(type)) {
            auto scope = getParentScope();
            auto typeSyntax = targetType.getTypeSyntax();
            SLANG_ASSERT(scope && typeSyntax);

            auto& diag = scope->addDiag(diag::TypeRestrictionMismatch, typeSyntax->sourceRange());
            diag << SemanticFacts::getTypeRestrictionText(typeRestriction);
            diag << type;

            if (isOverridden())
                diag.addNote(diag::NoteDeclarationHere, location);
        }
    }
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
                if (!inst || !inst->flags.has(InstanceFlags::ParentFromBind))
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

        isInsideBind |= body.flags.has(InstanceFlags::ParentFromBind);

        // We are also disallowed from having defparams inside an instance that has interface
        // ports that connect to an array from extending outside that hierarchy.
        for (auto conn : body.parentInstance->getPortConnections()) {
            auto [connSym, modport] = conn->getIfaceConn();
            if (connSym &&
                (connSym->kind == SymbolKind::InstanceArray ||
                 (connSym->getParentScope() &&
                  connSym->getParentScope()->asSymbol().kind == SymbolKind::InstanceArray))) {
                return body.parentInstance;
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
    auto equalsRange = assignment.setter->equals.range();
    auto declType = param.getDeclaredType();
    auto typeSyntax = declType->getTypeSyntax();

    if (typeSyntax && typeSyntax->kind == SyntaxKind::ImplicitType) {
        ASTContext typeContext(*param.getParentScope(), LookupLocation::before(param));
        auto [expr, type] = Expression::bindImplicitParam(*typeSyntax, exprSyntax, equalsRange,
                                                          context, typeContext);
        initializer = expr;
    }
    else {
        initializer = &Expression::bindRValue(declType->getType(), exprSyntax, equalsRange,
                                              context);
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
        auto scope = getParentScope();
        SLANG_ASSERT(scope);

        ASTContext ctx(*scope, LookupLocation::before(*this), ASTFlags::SpecparamInitializer);

        if (evaluating) {
            SLANG_ASSERT(referencingRange.start());

            auto& diag = ctx.addDiag(diag::ConstEvalParamCycle, location) << name;
            diag.addNote(diag::NoteReferencedHere, referencingRange);
            return ConstantValue::Invalid;
        }

        evaluating = true;
        auto guard = ScopeGuard([this] { evaluating = false; });

        // If no value has been explicitly set, try to set it
        // from our initializer.
        auto init = getInitializer();
        if (init) {
            auto& comp = scope->getCompilation();
            value1 = comp.allocConstant(ctx.eval(*init));

            // Specparams can also be a "PATHPULSE$" which has two values to bind.
            auto syntax = getSyntax();
            SLANG_ASSERT(syntax);

            auto& decl = syntax->as<SpecparamDeclaratorSyntax>();
            if (auto exprSyntax = decl.value2) {
                auto& expr2 = Expression::bindRValue(getType(), *exprSyntax, decl.equals.range(),
                                                     ctx);
                value2 = comp.allocConstant(ctx.eval(expr2));
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

    auto dir = isSource ? SpecifyBlockSymbol::SpecifyTerminalDir::Input
                        : SpecifyBlockSymbol::SpecifyTerminalDir::Output;
    auto& value = symbol->as<ValueSymbol>();
    if (!SpecifyBlockSymbol::checkPathTerminal(value, value.getType(), *parentParent, dir,
                                               sourceRange)) {
        return nullptr;
    }

    return symbol;
}

} // namespace slang::ast
