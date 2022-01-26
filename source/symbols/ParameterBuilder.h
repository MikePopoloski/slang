//------------------------------------------------------------------------------
// ParameterBuilder.h
// Helper for constructing parameter symbols
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/compilation/Definition.h"
#include "slang/util/StackContainer.h"

namespace slang {

class ParameterSymbolBase;
class Scope;
class Type;
struct ExpressionSyntax;
struct ParamOverrideNode;
struct ParameterDeclarationBaseSyntax;
struct ParameterPortListSyntax;
struct ParameterValueAssignmentSyntax;

/// This is a helper type for turning parameter-related syntax nodes into actual
/// parameter symbols and applying values to them. The logic here is factored out
/// so that it can be shared by both module/interface definitions as well as
/// generic class definitions.
class ParameterBuilder {
public:
    using Decl = Definition::ParameterDecl;

    ParameterBuilder(const Scope& scope, string_view definitionName,
                     span<const Decl> parameterDecls);

    bool hasErrors() const { return anyErrors; }

    void setAssignments(const ParameterValueAssignmentSyntax& syntax);
    void setOverrides(const ParamOverrideNode* newVal) { overrideNode = newVal; }
    void setForceInvalidValues(bool set) { forceInvalidValues = set; }
    void setSuppressErrors(bool set) { suppressErrors = set; }
    void setInstanceContext(const BindContext& context) { instanceContext = &context; }

    const ParamOverrideNode* getOverrides() const { return overrideNode; }

    const ParameterSymbolBase& createParam(const Definition::ParameterDecl& decl, Scope& newScope,
                                           SourceLocation instanceLoc);

    static void createDecls(const Scope& scope, const ParameterDeclarationBaseSyntax& syntax,
                            bool isLocal, bool isPort, SmallVector<Decl>& results);
    static void createDecls(const Scope& scope, const ParameterPortListSyntax& syntax,
                            SmallVector<Decl>& results);

private:
    const Scope& scope;
    string_view definitionName;
    span<const Decl> parameterDecls;
    SmallMap<string_view, const ExpressionSyntax*, 8> assignments;
    const BindContext* instanceContext = nullptr;
    const ParamOverrideNode* overrideNode = nullptr;
    bool forceInvalidValues = false;
    bool suppressErrors = false;
    bool anyErrors = false;
};

} // namespace slang
