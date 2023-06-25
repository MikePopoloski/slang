//------------------------------------------------------------------------------
// ParameterBuilder.cpp
// Helper for constructing parameter symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "ParameterBuilder.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Scope.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

ParameterBuilder::ParameterBuilder(const Scope& scope, std::string_view definitionName,
                                   std::span<const Decl> parameterDecls) :
    scope(scope),
    definitionName(definitionName), parameterDecls(parameterDecls) {
}

void ParameterBuilder::setAssignments(const ParameterValueAssignmentSyntax& syntax) {
    // Build up data structures to easily index the parameter assignments. We need to handle
    // both ordered assignment as well as named assignment, though a specific instance can only
    // use one method or the other.
    bool hasParamAssignments = false;
    bool orderedAssignments = true;
    SmallVector<const OrderedParamAssignmentSyntax*> orderedParams;
    SmallMap<std::string_view, std::pair<const NamedParamAssignmentSyntax*, bool>, 8> namedParams;

    for (auto paramBase : syntax.parameters) {
        bool isOrdered = paramBase->kind == SyntaxKind::OrderedParamAssignment;
        if (!hasParamAssignments) {
            hasParamAssignments = true;
            orderedAssignments = isOrdered;
        }
        else if (isOrdered != orderedAssignments) {
            scope.addDiag(diag::MixingOrderedAndNamedParams, paramBase->getFirstToken().location());
            break;
        }

        if (isOrdered)
            orderedParams.push_back(&paramBase->as<OrderedParamAssignmentSyntax>());
        else {
            auto& nas = paramBase->as<NamedParamAssignmentSyntax>();
            auto name = nas.name.valueText();
            if (!name.empty()) {
                auto pair = namedParams.emplace(name, std::make_pair(&nas, false));
                if (!pair.second) {
                    auto& diag = scope.addDiag(diag::DuplicateParamAssignment, nas.name.location());
                    diag << name;
                    diag.addNote(diag::NotePreviousUsage,
                                 pair.first->second.first->name.location());
                }
            }
        }
    }

    // For each parameter assignment we have, match it up to a real parameter
    if (orderedAssignments) {
        uint32_t orderedIndex = 0;
        for (auto& param : parameterDecls) {
            if (orderedIndex >= orderedParams.size())
                break;

            if (param.isLocalParam)
                continue;

            assignments.emplace(param.name, orderedParams[orderedIndex++]->expr);
        }

        // Make sure there aren't extra param assignments for non-existent params.
        if (orderedIndex < orderedParams.size()) {
            auto loc = orderedParams[orderedIndex]->getFirstToken().location();
            auto& diag = scope.addDiag(diag::TooManyParamAssignments, loc);
            diag << definitionName;
            diag << orderedParams.size();
            diag << orderedIndex;
        }
    }
    else {
        // Otherwise handle named assignments.
        for (auto& param : parameterDecls) {
            auto it = namedParams.find(param.name);
            if (it == namedParams.end())
                continue;

            auto arg = it->second.first;
            it->second.second = true;
            if (param.isLocalParam) {
                // Can't assign to localparams, so this is an error.
                DiagCode code = param.isPortParam ? diag::AssignedToLocalPortParam
                                                  : diag::AssignedToLocalBodyParam;

                auto& diag = scope.addDiag(code, arg->name.location());
                diag.addNote(diag::NoteDeclarationHere, param.location);
                continue;
            }

            // It's allowed to have no initializer in the assignment; it means to just use the
            // default.
            if (!arg->expr)
                continue;

            assignments.emplace(param.name, arg->expr);
        }

        for (auto& pair : namedParams) {
            // We marked all the args that we used, so anything left over is a param assignment
            // for a non-existent parameter.
            auto [argSyntax, used] = pair.second;
            if (!used) {
                auto& diag = scope.addDiag(diag::ParameterDoesNotExist, argSyntax->name.location());
                diag << argSyntax->name.valueText();
                diag << definitionName;
            }
        }
    }
}

const ParameterSymbolBase& ParameterBuilder::createParam(const Definition::ParameterDecl& decl,
                                                         Scope& newScope,
                                                         SourceLocation instanceLoc) {
    auto reportError = [&](auto& param) {
        anyErrors = true;
        if (!suppressErrors && !param.name.empty()) {
            auto& diag = scope.addDiag(diag::ParamHasNoValue, instanceLoc);
            diag << definitionName;
            diag << param.name;
        }
    };

    auto& comp = scope.getCompilation();
    const ExpressionSyntax* newInitializer = nullptr;
    if (auto it = assignments.find(decl.name); it != assignments.end())
        newInitializer = it->second;

    if (decl.isTypeParam) {
        auto param = comp.emplace<TypeParameterSymbol>(decl.name, decl.location, decl.isLocalParam,
                                                       decl.isPortParam);
        param->setAttributes(scope, decl.attributes);

        auto& tt = param->targetType;
        if (newInitializer) {
            // If this is a NameSyntax, the parser didn't know we were assigning to
            // a type parameter, so fix it up into a NamedTypeSyntax to get a type from it.
            tt.addFlags(DeclaredTypeFlags::TypeOverridden);
            if (NameSyntax::isKind(newInitializer->kind)) {
                // const_cast is ugly but safe here, we're only going to refer to it
                // by const reference everywhere down.
                auto& nameSyntax = const_cast<NameSyntax&>(newInitializer->as<NameSyntax>());
                auto namedType = comp.emplace<NamedTypeSyntax>(nameSyntax);

                tt.setTypeSyntax(*namedType);
            }
            else if (!DataTypeSyntax::isKind(newInitializer->kind)) {
                tt.setType(comp.getErrorType());
                scope.addDiag(diag::BadTypeParamExpr, newInitializer->getFirstToken().location())
                    << param->name;
            }
            else {
                tt.setTypeSyntax(newInitializer->as<DataTypeSyntax>());
            }
        }
        else if (!decl.hasSyntax) {
            if (decl.givenType)
                tt.setType(*decl.givenType);
            else
                tt.setType(comp.getErrorType());
        }
        else {
            SLANG_ASSERT(decl.typeDecl);
            param->setSyntax(*decl.typeDecl);
            if (decl.typeDecl->assignment)
                tt.setTypeSyntax(*decl.typeDecl->assignment->type);
            else
                tt.setType(comp.getErrorType());
        }

        // Add to scope *after* setting the type on the member,
        // so that enums get picked up correctly.
        newScope.addMember(*param);

        if (!param->isLocalParam()) {
            if (forceInvalidValues) {
                tt.setType(comp.getErrorType());
            }
            else if (newInitializer) {
                if (instanceContext)
                    tt.forceResolveAt(*instanceContext);
            }
            else if (param->isPortParam() && !tt.getTypeSyntax() &&
                     (decl.hasSyntax || !decl.givenType)) {
                reportError(*param);
            }
        }

        return *param;
    }
    else {
        auto param = comp.emplace<ParameterSymbol>(decl.name, decl.location, decl.isLocalParam,
                                                   decl.isPortParam);
        param->setAttributes(scope, decl.attributes);

        auto& declType = *param->getDeclaredType();
        if (newInitializer)
            declType.addFlags(DeclaredTypeFlags::InitializerOverridden);

        if (!decl.hasSyntax) {
            SLANG_ASSERT(decl.givenType);
            param->setType(*decl.givenType);
            if (decl.givenInitializer)
                param->setInitializer(*decl.givenInitializer);
        }
        else {
            SLANG_ASSERT(decl.valueSyntax);
            SLANG_ASSERT(decl.valueDecl);

            param->setDeclaredType(*decl.valueSyntax->type);
            param->setFromDeclarator(*decl.valueDecl);
        }

        if (newInitializer) {
            param->setInitializerSyntax(*newInitializer,
                                        newInitializer->getFirstToken().location());
        }

        // Add to scope *after* setting the type on the member,
        // so that enums get picked up correctly.
        newScope.addMember(*param);

        // If there is an override node, see if this parameter is in it.
        if (auto paramSyntax = param->getSyntax(); overrideNode && paramSyntax) {
            auto& map = overrideNode->overrides;
            if (auto it = map.find(paramSyntax); it != map.end()) {
                param->setValue(comp, it->second.first, /* needsCoercion */ true);
                return *param;
            }
        }

        if (!param->isLocalParam()) {
            if (forceInvalidValues) {
                param->setValue(comp, nullptr, /* needsCoercion */ false);
            }
            else if (newInitializer) {
                if (instanceContext)
                    declType.resolveAt(*instanceContext);
            }
            else if (param->isPortParam() && !declType.getInitializerSyntax()) {
                reportError(*param);
            }
        }

        return *param;
    }
}

void ParameterBuilder::createDecls(const Scope& scope, const ParameterDeclarationBaseSyntax& syntax,
                                   bool isLocal, bool isPort,
                                   std::span<const AttributeInstanceSyntax* const> attributes,
                                   SmallVectorBase<Decl>& results) {
    if (syntax.kind == SyntaxKind::ParameterDeclaration) {
        auto& paramSyntax = syntax.as<ParameterDeclarationSyntax>();
        for (auto decl : paramSyntax.declarators)
            results.emplace_back(scope, paramSyntax, *decl, isLocal, isPort, attributes);
    }
    else {
        auto& paramSyntax = syntax.as<TypeParameterDeclarationSyntax>();
        for (auto decl : paramSyntax.declarators)
            results.emplace_back(scope, paramSyntax, *decl, isLocal, isPort, attributes);
    }
}

void ParameterBuilder::createDecls(const Scope& scope, const ParameterPortListSyntax& syntax,
                                   SmallVectorBase<Decl>& results) {
    bool lastLocal = false;
    for (auto declaration : syntax.declarations) {
        // It's legal to leave off the parameter keyword in the parameter port list.
        // If you do so, we "inherit" the parameter or localparam keyword from the
        // previous entry.
        if (declaration->keyword) {
            lastLocal = declaration->keyword.kind == parsing::TokenKind::LocalParamKeyword;
        }

        createDecls(scope, *declaration, lastLocal, /* isPort */ true, {}, results);
    }
}

} // namespace slang::ast
