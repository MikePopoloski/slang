//------------------------------------------------------------------------------
// Definition.h
// Module / interface / program definition metadata.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "parsing/AllSyntax.h"
#include "text/SourceLocation.h"
#include "util/Util.h"

namespace slang {

/// Represents a definition (module, interface, or program) that can be instantiated
/// to form a node in the design hierarchy.
class Definition {
public:
    /// The syntax that defines the body of the definition.
    const ModuleDeclarationSyntax& syntax;

    /// The name of the definition.
    string_view name;

    /// Tracks info about each parameter declaration for later evaluation.
    struct ParameterDecl {
        /// The name of the parameter.
        string_view name;

        /// The syntax describing the parameter's data type. This is evaluated lazily
        /// into a real type since it may require doing inference from the value.
        const DataTypeSyntax* type = nullptr;

        /// The default initializer, or null if the parameter has no default.
        const ExpressionSyntax* initializer = nullptr;

        /// The source location of the parameter.
        SourceLocation location;

        /// Indicates whether the parameter is a localparam (not overridable).
        bool isLocal;

        /// Indicates whether the parameter was declared in the header (parameter port list) or
        /// within the body of the definition itself.
        bool isPort;
    };

    /// A list of parameter declarations within the definition.
    span<const ParameterDecl> parameters;

    explicit Definition(const ModuleDeclarationSyntax& syntax) :
        syntax(syntax), name(syntax.header->name.valueText()) {}
};

}