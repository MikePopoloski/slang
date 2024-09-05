//------------------------------------------------------------------------------
// ParameterBuilder.h
// Helper for constructing parameter symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/symbols/CompilationUnitSymbols.h"

namespace slang::ast {

class ParameterSymbolBase;
class Scope;
struct HierarchyOverrideNode;

/// This is a helper type for turning parameter-related syntax nodes into actual
/// parameter symbols and applying values to them. The logic here is factored out
/// so that it can be shared by both module/interface definitions as well as
/// generic class definitions.
class ParameterBuilder {
public:
    using Decl = DefinitionSymbol::ParameterDecl;

    ParameterBuilder(const Scope& scope, std::string_view definitionName,
                     std::span<const Decl> parameterDecls);

    bool hasErrors() const { return anyErrors; }

    void setAssignments(const syntax::ParameterValueAssignmentSyntax& syntax, bool isFromConfig);
    void setOverrides(const HierarchyOverrideNode* newVal) { overrideNode = newVal; }
    void setForceInvalidValues(bool set) { forceInvalidValues = set; }
    void setSuppressErrors(bool set) { suppressErrors = set; }
    void setInstanceContext(const ASTContext& context) { instanceContext = &context; }
    void setConfigScope(const Scope& confScope) { configScope = &confScope; }

    const HierarchyOverrideNode* getOverrides() const { return overrideNode; }

    const ParameterSymbolBase& createParam(const DefinitionSymbol::ParameterDecl& decl,
                                           Scope& newScope, SourceLocation instanceLoc);

    static void createDecls(const Scope& scope,
                            const syntax::ParameterDeclarationBaseSyntax& syntax, bool isLocal,
                            bool isPort,
                            std::span<const syntax::AttributeInstanceSyntax* const> attributes,
                            SmallVectorBase<Decl>& results);
    static void createDecls(const Scope& scope, const syntax::ParameterPortListSyntax& syntax,
                            SmallVectorBase<Decl>& results);

private:
    const Scope& scope;
    std::string_view definitionName;
    std::span<const Decl> parameterDecls;
    SmallMap<std::string_view, std::pair<const syntax::ExpressionSyntax*, bool>, 8> assignments;
    const ASTContext* instanceContext = nullptr;
    const HierarchyOverrideNode* overrideNode = nullptr;
    const Scope* configScope = nullptr;
    bool forceInvalidValues = false;
    bool suppressErrors = false;
    bool anyErrors = false;
};

} // namespace slang::ast
