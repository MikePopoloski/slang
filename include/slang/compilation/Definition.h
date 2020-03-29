//------------------------------------------------------------------------------
//! @file Definition.h
//! @brief Module / interface / program definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

#include "slang/symbols/Lookup.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

class AttributeSymbol;
class Compilation;
class NetType;
class Scope;

struct DeclaratorSyntax;
struct ModuleDeclarationSyntax;
struct ParameterDeclarationSyntax;
struct TypeAssignmentSyntax;
struct TypeParameterDeclarationSyntax;

class Definition {
public:
    string_view name;
    SourceLocation location;
    const ModuleDeclarationSyntax& syntax;
    const NetType& defaultNetType;
    const Scope& scope;
    SymbolIndex indexInScope;
    DefinitionKind definitionKind;
    VariableLifetime defaultLifetime;
    UnconnectedDrive unconnectedDrive;
    TimeScale timeScale;

    struct ParameterDecl {
        union {
            const ParameterDeclarationSyntax* valueSyntax;
            const TypeParameterDeclarationSyntax* typeSyntax;
        };

        union {
            const DeclaratorSyntax* valueDecl;
            const TypeAssignmentSyntax* typeDecl;
        };

        string_view name;
        SourceLocation location;
        bool isTypeParam;
        bool isLocalParam;
        bool isPortParam;

        ParameterDecl(const Scope& scope, const ParameterDeclarationSyntax& syntax,
                      const DeclaratorSyntax& decl, bool isLocal, bool isPort);
        ParameterDecl(const Scope& scope, const TypeParameterDeclarationSyntax& syntax,
                      const TypeAssignmentSyntax& decl, bool isLocal, bool isPort);

        bool hasDefault() const;
    };

    SmallVectorSized<ParameterDecl, 8> parameters;
    flat_hash_set<string_view> modports;
    span<const AttributeSymbol* const> attributes;

    Definition(const Scope& scope, LookupLocation lookupLocation,
               const ModuleDeclarationSyntax& syntax, const NetType& defaultNetType,
               UnconnectedDrive unconnectedDrive, optional<TimeScale> directiveTimeScale);
};

} // namespace slang