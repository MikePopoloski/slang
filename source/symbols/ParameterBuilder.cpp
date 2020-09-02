//------------------------------------------------------------------------------
// ParameterBuilder.cpp
// Helper for constructing parameter symbols
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "ParameterBuilder.h"

#include "slang/binding/BindContext.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

void ParameterBuilder::setAssignments(const ParameterValueAssignmentSyntax& syntax) {
    // Build up data structures to easily index the parameter assignments. We need to handle
    // both ordered assignment as well as named assignment, though a specific instance can only
    // use one method or the other.
    bool hasParamAssignments = false;
    bool orderedAssignments = true;
    SmallVectorSized<const OrderedArgumentSyntax*, 8> orderedParams;
    SmallMap<string_view, std::pair<const NamedArgumentSyntax*, bool>, 8> namedParams;

    for (auto paramBase : syntax.assignments->parameters) {
        bool isOrdered = paramBase->kind == SyntaxKind::OrderedArgument;
        if (!hasParamAssignments) {
            hasParamAssignments = true;
            orderedAssignments = isOrdered;
        }
        else if (isOrdered != orderedAssignments) {
            scope.addDiag(diag::MixingOrderedAndNamedParams, paramBase->getFirstToken().location());
            break;
        }

        if (isOrdered)
            orderedParams.append(&paramBase->as<OrderedArgumentSyntax>());
        else {
            const NamedArgumentSyntax& nas = paramBase->as<NamedArgumentSyntax>();
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

            overrides.emplace(param.name, orderedParams[orderedIndex++]->expr);
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

            const NamedArgumentSyntax* arg = it->second.first;
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

            overrides.emplace(param.name, arg->expr);
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

void ParameterBuilder::createParams(Scope& newScope, LookupLocation lookupLocation,
                                    SourceLocation instanceLoc, bool forceInvalidValues) {
    auto& compilation = scope.getCompilation();
    BindContext context(scope, lookupLocation, BindFlags::Constant);

    for (auto& param : parameterDecls) {
        if (!param.isTypeParam) {
            // This is a value parameter.
            const ExpressionSyntax* newInitializer = nullptr;
            if (auto it = overrides.find(param.name); it != overrides.end())
                newInitializer = it->second;

            auto& newParam = ParameterSymbol::fromDecl(param, newScope, context, newInitializer);
            paramSymbols.append(&newParam);
            if (newParam.isLocalParam())
                continue;

            if (forceInvalidValues) {
                paramValues.append(&ConstantValue::Invalid);
                continue;
            }

            // For all port params, if we were provided a parameter override save
            // that value now for use with the cache key. Otherwise use a nullptr
            // to represent that the default will be used. We can't evaluate the
            // default now because it might depend on other members that haven't
            // been created yet.
            if (newInitializer)
                paramValues.append(&newParam.getValue());
            else
                paramValues.append(nullptr);

            if (newParam.isPortParam() && !newParam.getDeclaredType()->getInitializerSyntax()) {
                auto& diag = scope.addDiag(diag::ParamHasNoValue, instanceLoc);
                diag << definitionName;
                diag << newParam.name;
            }
        }
        else {
            // Otherwise this is a type parameter.
            const ExpressionSyntax* newInitializer = nullptr;
            if (auto it = overrides.find(param.name); it != overrides.end())
                newInitializer = it->second;

            auto& newParam =
                TypeParameterSymbol::fromDecl(param, newScope, context, newInitializer);
            paramSymbols.append(&newParam);
            if (newParam.isLocalParam())
                continue;

            if (forceInvalidValues) {
                typeParams.append(&compilation.getErrorType());
                continue;
            }

            if (newInitializer)
                typeParams.append(&newParam.targetType.getType());
            else
                typeParams.append(nullptr);

            if (!newInitializer && newParam.isPortParam() && !newParam.targetType.getTypeSyntax()) {
                auto& diag = scope.addDiag(diag::ParamHasNoValue, instanceLoc);
                diag << definitionName;
                diag << newParam.name;
            }
        }
    }
}

void ParameterBuilder::createDecls(const Scope& scope, const ParameterDeclarationBaseSyntax& syntax,
                                   bool isLocal, bool isPort, SmallVector<Decl>& results) {
    if (syntax.kind == SyntaxKind::ParameterDeclaration) {
        auto& paramSyntax = syntax.as<ParameterDeclarationSyntax>();
        for (auto decl : paramSyntax.declarators)
            results.emplace(scope, paramSyntax, *decl, isLocal, isPort);
    }
    else {
        auto& paramSyntax = syntax.as<TypeParameterDeclarationSyntax>();
        for (auto decl : paramSyntax.declarators)
            results.emplace(scope, paramSyntax, *decl, isLocal, isPort);
    }
}

void ParameterBuilder::createDecls(const Scope& scope, const ParameterPortListSyntax& syntax,
                                   SmallVector<Decl>& results) {
    bool lastLocal = false;
    for (auto declaration : syntax.declarations) {
        // It's legal to leave off the parameter keyword in the parameter port list.
        // If you do so, we "inherit" the parameter or localparam keyword from the
        // previous entry.
        if (declaration->keyword)
            lastLocal = declaration->keyword.kind == TokenKind::LocalParamKeyword;

        createDecls(scope, *declaration, lastLocal, /* isPort */ true, results);
    }
}

} // namespace slang
