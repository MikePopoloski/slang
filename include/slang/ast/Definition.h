//------------------------------------------------------------------------------
//! @file Definition.h
//! @brief Module / interface / program definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/SemanticFacts.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Hash.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang::syntax {
class SyntaxTree;
}

namespace slang::ast {

class AttributeSymbol;
class Expression;
class LookupLocation;
class NetType;
class Scope;
class Type;
enum class SymbolIndex : uint32_t;

/// Represents a module, interface, or program definition.
class SLANG_EXPORT Definition {
public:
    /// Information about a single parameter declaration.
    struct ParameterDecl {
        union {
            const syntax::ParameterDeclarationSyntax* valueSyntax;
            const syntax::TypeParameterDeclarationSyntax* typeSyntax;
            const Type* givenType;
        };

        union {
            const syntax::DeclaratorSyntax* valueDecl;
            const syntax::TypeAssignmentSyntax* typeDecl;
            const Expression* givenInitializer;
        };

        /// The name of the parameter.
        std::string_view name;

        /// The source location where the parameter is defined.
        SourceLocation location;

        /// Attributes associated with the parameter.
        std::span<const syntax::AttributeInstanceSyntax* const> attributes;

        /// True if this is a type parameter.
        bool isTypeParam;

        /// True if this is a localparam.
        bool isLocalParam;

        /// True if this parameter is declared in the definition's port list.
        bool isPortParam;

        /// True if there is a syntax node associated with this parameter. This controls
        /// which members of the unions are valid.
        bool hasSyntax;

        /// Constructs a new ParameterDecl instance.
        ParameterDecl(const Scope& scope, const syntax::ParameterDeclarationSyntax& syntax,
                      const syntax::DeclaratorSyntax& decl, bool isLocal, bool isPort,
                      std::span<const syntax::AttributeInstanceSyntax* const> attributes);

        /// Constructs a new ParameterDecl instance.
        ParameterDecl(const Scope& scope, const syntax::TypeParameterDeclarationSyntax& syntax,
                      const syntax::TypeAssignmentSyntax& decl, bool isLocal, bool isPort,
                      std::span<const syntax::AttributeInstanceSyntax* const> attributes);

        /// Constructs a new ParameterDecl instance.
        ParameterDecl(std::string_view name, SourceLocation location, const Type& givenType,
                      bool isLocal, bool isPort, const Expression* givenInitializer);

        /// Constructs a new ParameterDecl instance.
        ParameterDecl(std::string_view name, SourceLocation location, bool isLocal, bool isPort,
                      const Type* defaultType);

        /// Indicates whether this parameter has a default value expression.
        bool hasDefault() const;
    };

    /// The name of the definition.
    std::string_view name;

    /// The source location where the definition is declared.
    SourceLocation location;

    /// The syntax node describing the definition.
    const syntax::ModuleDeclarationSyntax& syntax;

    /// The default nettype for implicit nets within this definition.
    const NetType& defaultNetType;

    /// The scope containing the definition.
    const Scope& scope;

    /// The index of this definition within its parent scope.
    SymbolIndex indexInScope;

    /// The kind of definition (module, interface, or program).
    DefinitionKind definitionKind;

    /// The default lifetime for variables declared within this definition.
    VariableLifetime defaultLifetime;

    /// The drive setting to use for unconnected nets within this definition.
    UnconnectedDrive unconnectedDrive;

    /// The timescale specified for this definition, or nullopt if none
    /// is explicitly specified.
    std::optional<TimeScale> timeScale;

    /// A list of parameters declared by this definition.
    SmallVector<ParameterDecl, 8> parameters;

    /// A list of ports declared by this definition.
    const syntax::PortListSyntax* portList;

    /// A set of modport names declared by this definition.
    flat_hash_set<std::string_view> modports;

    /// A set of attributes associated with this definition.
    std::span<const AttributeSymbol* const> attributes;

    /// A set of bind directives that apply to all instances of this definition.
    std::vector<const syntax::BindDirectiveSyntax*> bindDirectives;

    /// The syntax tree that contains this definition, or nullptr if constructed
    /// outside of any specific syntax tree.
    const syntax::SyntaxTree* syntaxTree;

    /// Indicates whether this definition has non-ansi port declarations.
    bool hasNonAnsiPorts;

    /// Constructs a new instance of the Definition class.
    Definition(const Scope& scope, LookupLocation lookupLocation,
               const syntax::ModuleDeclarationSyntax& syntax, const NetType& defaultNetType,
               UnconnectedDrive unconnectedDrive, std::optional<TimeScale> directiveTimeScale,
               const syntax::SyntaxTree* syntaxTree);

    /// Returns a string description of the definition kind, such as "module",
    /// "interface", or "program".
    std::string_view getKindString() const;

    /// Returns a string description of the definition kind, including an
    /// indefinite article. e.g. "a module", "an interface".
    std::string_view getArticleKindString() const;

    /// Returns true if the definition has been instantiated anywhere in the design.
    bool isInstantiated() const { return instantiated; }

    /// Notes that the definition has been instantiated.
    void noteInstantiated() const { instantiated = true; }

    /// Gets the hierarchical path to the definition, appending it
    /// to the provided string.
    void getHierarchicalPath(std::string& buffer) const;

private:
    mutable bool instantiated = false;
};

} // namespace slang::ast
