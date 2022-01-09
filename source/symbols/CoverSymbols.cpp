//------------------------------------------------------------------------------
// CoverSymbols.cpp
// Contains coverage-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/CoverSymbols.h"

#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

CovergroupType::CovergroupType(Compilation& compilation, string_view name, SourceLocation loc,
                               const CovergroupBodySymbol& body) :
    Type(SymbolKind::CovergroupType, name, loc),
    Scope(compilation, this), body(body) {
}

const Symbol& CovergroupType::fromSyntax(const Scope& scope,
                                         const CovergroupDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto body = comp.emplace<CovergroupBodySymbol>(comp, syntax.name.location());
    auto result =
        comp.emplace<CovergroupType>(comp, syntax.name.valueText(), syntax.name.location(), *body);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    if (syntax.portList) {
        SmallVectorSized<const FormalArgumentSymbol*, 8> args;
        SubroutineSymbol::buildArguments(*result, *syntax.portList, VariableLifetime::Automatic,
                                         args);
        result->arguments = args.copy(comp);

        for (auto arg : result->arguments) {
            if (arg->direction == ArgumentDirection::Out ||
                arg->direction == ArgumentDirection::InOut) {
                scope.addDiag(diag::CovergroupOutArg, arg->location);
            }
        }
    }

    result->addMember(*body);
    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::CoverageOption) {
            // TODO: handle options
        }
        else {
            body->addMembers(*member);
        }
    }

    return *result;
}

const TimingControl* CovergroupType::getCoverageEvent() const {
    if (event)
        return *event;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    if (scope && syntax) {
        if (auto evSyntax = syntax->as<CovergroupDeclarationSyntax>().event) {
            LookupLocation ll = LookupLocation::min;
            if (!arguments.empty())
                ll = LookupLocation::after(*arguments.back());

            BindContext context(*this, ll);

            if (evSyntax->kind == SyntaxKind::BlockCoverageEvent) {
                event = &BlockEventListControl::fromSyntax(
                    *evSyntax->as<BlockCoverageEventSyntax>().expr, context);
                return *event;
            }
            else if (evSyntax->kind == SyntaxKind::EventControlWithExpression) {
                event =
                    &TimingControl::bind(evSyntax->as<EventControlWithExpressionSyntax>(), context);
                return *event;
            }
        }
    }

    event = nullptr;
    return nullptr;
}

ConstantValue CovergroupType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

void CovergroupType::serializeTo(ASTSerializer&) const {
    // TODO:
}

CoverpointSymbol::CoverpointSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Coverpoint, name, loc), Scope(compilation, this),
    declaredType(*this, DeclaredTypeFlags::InferImplicit | DeclaredTypeFlags::AutomaticInitializer |
                            DeclaredTypeFlags::CoverageType) {

    // Set the overrideIndex for the type and expression so that they cannot refer to
    // other members of the parent covergroup. This allows coverpoints named the same
    // as formal arguments to not interfere with lookup.
    declaredType.setOverrideIndex(SymbolIndex(1));
}

CoverpointSymbol& CoverpointSymbol::fromSyntax(const Scope& scope, const CoverpointSyntax& syntax) {
    // It's possible for invalid syntax to parse as a coverpoint. If the keyword wasn't
    // given just give up and return a placeholder.
    auto& comp = scope.getCompilation();
    if (syntax.coverpoint.isMissing())
        return *comp.emplace<CoverpointSymbol>(comp, ""sv, syntax.getFirstToken().location());

    // Figure out the name of the coverpoint. If there's a label, it provides the name.
    // Otherwise check if the expression is a simple variable reference. If so, we take
    // that variable name as the name of the coverpoint. Otherwise it's unnamed.
    string_view name;
    SourceLocation loc;
    if (syntax.label) {
        name = syntax.label->name.valueText();
        loc = syntax.label->name.location();
    }
    else if (syntax.expr->kind == SyntaxKind::IdentifierName) {
        auto id = syntax.expr->as<IdentifierNameSyntax>().identifier;
        name = id.valueText();
        loc = id.location();
    }
    else {
        loc = syntax.expr->getFirstToken().location();
    }

    auto result = comp.emplace<CoverpointSymbol>(comp, name, loc);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    result->declaredType.setTypeSyntax(*syntax.type);
    result->declaredType.setInitializerSyntax(*syntax.expr,
                                              syntax.expr->getFirstToken().location());

    return *result;
}

CoverpointSymbol& CoverpointSymbol::fromImplicit(const Scope& scope,
                                                 const IdentifierNameSyntax& syntax) {
    auto loc = syntax.identifier.location();
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CoverpointSymbol>(comp, syntax.identifier.valueText(), loc);

    result->declaredType.setTypeSyntax(comp.createEmptyTypeSyntax(loc));
    result->declaredType.setInitializerSyntax(syntax, loc);
    return *result;
}

const Expression* CoverpointSymbol::getIffExpr() const {
    if (!iffExpr) {
        auto scope = getParentScope();
        auto syntax = getSyntax();
        ASSERT(scope);

        if (!syntax)
            iffExpr = nullptr;
        else {
            auto iffSyntax = syntax->as<CoverpointSyntax>().iff;
            if (!iffSyntax)
                iffExpr = nullptr;
            else {
                BindContext context(*scope, LookupLocation::min);
                iffExpr = &Expression::bind(*iffSyntax->expr, context);
                context.requireBooleanConvertible(*iffExpr.value());
            }
        }
    }
    return *iffExpr;
}

void CoverpointSymbol::serializeTo(ASTSerializer&) const {
    // TODO:
}

void CoverCrossSymbol::fromSyntax(const Scope& scope, const CoverCrossSyntax& syntax,
                                  SmallVector<const Symbol*>& results) {
    string_view name;
    SourceLocation loc;
    if (syntax.label) {
        name = syntax.label->name.valueText();
        loc = syntax.label->name.location();
    }
    else {
        loc = syntax.cross.location();
    }

    SmallVectorSized<const CoverpointSymbol*, 4> targets;
    for (auto item : syntax.items) {
        auto id = item->identifier;
        auto symbol = Lookup::unqualifiedAt(scope, id.valueText(), LookupLocation::max, id.range());
        if (symbol) {
            if (symbol->kind == SymbolKind::Coverpoint) {
                targets.append(&symbol->as<CoverpointSymbol>());
            }
            else {
                // If we didn't find a coverpoint, create one implicitly
                // that will be initialized with this expression.
                auto& newPoint = CoverpointSymbol::fromImplicit(scope, *item);
                targets.append(&newPoint);
                results.append(&newPoint);
            }
        }
    }

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CoverCrossSymbol>(comp, name, loc, targets.copy(comp));
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    results.append(result);
}

const Expression* CoverCrossSymbol::getIffExpr() const {
    if (!iffExpr) {
        auto scope = getParentScope();
        auto syntax = getSyntax();
        ASSERT(scope);

        if (!syntax)
            iffExpr = nullptr;
        else {
            auto iffSyntax = syntax->as<CoverCrossSyntax>().iff;
            if (!iffSyntax)
                iffExpr = nullptr;
            else {
                BindContext context(*scope, LookupLocation::min);
                iffExpr = &Expression::bind(*iffSyntax->expr, context);
                context.requireBooleanConvertible(*iffExpr.value());
            }
        }
    }
    return *iffExpr;
}

void CoverCrossSymbol::serializeTo(ASTSerializer&) const {
    // TODO:
}

} // namespace slang
