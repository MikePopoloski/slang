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

    /// Class and checker declarations at any scope. Module-like declarations are in @a nodeMeta.
    std::vector<const syntax::SyntaxNode*> decls;

    /// Potential dependency references: hierarchy and checker instantiations, identifier names
    /// preceding a double colon, package import declarations, and virtual interface types.
    /// Hierarchy instantiations are included only for global modules/interfaces/programs.
    std::vector<const syntax::SyntaxNode*> refs;

    /// A list of all enum types parsed.
    std::vector<const syntax::EnumTypeSyntax*> enumTypes;

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

    /// Returns the unique symbol names from @a visitReferencedSymbols.
    std::vector<std::string_view> getReferencedSymbols() const;

    /// Visits all top level symbols referenced/used by this metadata, calling the provided
    /// function with each name token, including virtual interface types. Tokens retain source
    /// locations so callers can resolve dependencies relative to the referencing file.
    /// If @a includeInterfacePorts is true, also includes explicit interface port types.
    void visitReferencedSymbols(function_ref<void(Token)> func,
                                bool includeInterfacePorts = true) const;
};

} // namespace slang::parsing
