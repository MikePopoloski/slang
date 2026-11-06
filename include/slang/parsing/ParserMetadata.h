//------------------------------------------------------------------------------
//! @file ParserMetadata.h
//! @brief Metadata collected during parsing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <optional>
#include <vector>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Function.h"
#include "slang/util/Util.h"

namespace slang::parsing {

/// Various bits of metadata collected during parsing.
struct SLANG_EXPORT ParserMetadata {
    /// Collection of metadata that can be associated with a syntax node at parse time.
    struct Node {
        TokenKind defaultNetType;
        TokenKind unconnectedDrive;
        bool cellDefine = false;
        std::optional<TimeScale> timeScale;
    };

    /// Specific metadata that was in effect when certain syntax nodes were parsed
    /// (such as various bits of preprocessor state).
    std::vector<std::pair<const syntax::ModuleDeclarationSyntax*, Node>> nodeMeta;

    /// A list of all instantiations of global modules/interfaces/programs.
    /// This can be used to determine which modules should be considered as top-level
    /// roots of the design, or to find references of a particular module.
    std::vector<const syntax::HierarchyInstantiationSyntax*> globalInstances;

    /// A list of all names parsed that could represent a package or class name,
    /// since they are simple names that appear on the left-hand side of a double colon.
    std::vector<const syntax::IdentifierNameSyntax*> classPackageNames;

    /// A list of all package import declarations parsed.
    std::vector<const syntax::PackageImportDeclarationSyntax*> packageImports;

    /// A list of all class declarations parsed.
    std::vector<const syntax::ClassDeclarationSyntax*> classDecls;

    /// A list of all checker declarations parsed.
    std::vector<const syntax::CheckerDeclarationSyntax*> checkerDecls;

    /// A list of *some* checker instantiations parsed. Checker instantiations
    /// in non-procedural contexts are generally indistinguishable from module
    /// instantiations and so are included in @a globalInstances instead.
    std::vector<const syntax::CheckerInstantiationSyntax*> checkerInstances;

    /// A list of all virtual interface types parsed.
    std::vector<const syntax::VirtualInterfaceTypeSyntax*> virtualInterfaceTypes;

    /// The EOF token, if one has already been consumed by the parser.
    /// Otherwise an empty token.
    Token eofToken;

    /// Indicates whether the parse tree has any defparam directives.
    bool hasDefparams = false;

    /// Indicates whether the parse tree has any bind directives.
    bool hasBindDirectives = false;

    /// Constructs a new set of parser metadata by walking the provided syntax tree.
    static ParserMetadata fromSyntax(const syntax::SyntaxNode& root);

    /// Returns a list of all symbols from @a visitDeclaredSymbols.
    std::vector<std::string_view> getDeclaredSymbols(bool includeNested = false) const;

    /// Visits compilation-unit module, interface, program, package, class, and checker
    /// declarations, calling the provided function with each unqualified name. If @a includeNested
    /// is true, also includes declarations within other scopes.
    void visitDeclaredSymbols(function_ref<void(std::string_view)> func,
                              bool includeNested = false) const;

    /// Returns a list of all symbols from @a visitReferencedSymbols.
    std::vector<std::string_view> getReferencedSymbols() const;

    /// Visits all top level symbols referenced/used by this metadata, calling the provided
    /// function for each symbol name, including virtual interface types.
    /// If @a includePortNames is true, also includes explicit interface ports and ambiguous
    /// variable port types that can resolve to interfaces or data types.
    void visitReferencedSymbols(function_ref<void(std::string_view)> func,
                                bool includePortNames = true) const;
};

} // namespace slang::parsing
