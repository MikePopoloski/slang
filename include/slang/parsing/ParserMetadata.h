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
#include "slang/util/Util.h"

namespace slang::parsing {

/// Various bits of metadata collected during parsing.
struct SLANG_EXPORT ParserMetadata {
    /// Collection of metadata that can be associated with a syntax node at parse time.
    struct Node {
        TokenKind defaultNetType;
        TokenKind unconnectedDrive;
        std::optional<TimeScale> timeScale;
    };

    /// Specific metadata that was in effect when certain syntax nodes were parsed
    /// (such as various bits of preprocessor state).
    flat_hash_map<const syntax::SyntaxNode*, Node> nodeMap;

    /// A set of names of all instantiations of global modules/interfaces/programs.
    /// This can be used to determine which modules should be considered as top-level
    /// roots of the design.
    flat_hash_set<std::string_view> globalInstances;

    /// A list of all names parsed that could represent a package or class name,
    /// since they are simple names that appear on the left-hand side of a double colon.
    std::vector<const syntax::IdentifierNameSyntax*> classPackageNames;

    /// A list of all package import declarations parsed.
    std::vector<const syntax::PackageImportDeclarationSyntax*> packageImports;

    /// A list of all class declarations parsed.
    std::vector<const syntax::ClassDeclarationSyntax*> classDecls;

    /// A list of all interface port headers parsed.
    std::vector<const syntax::InterfacePortHeaderSyntax*> interfacePorts;

    /// The EOF token, if one has already been consumed by the parser.
    /// Otherwise an empty token.
    Token eofToken;

    /// Indicates whether the parse tree has any defparam directives.
    bool hasDefparams = false;

    /// Indicates whether the parse tree has any bind directives.
    bool hasBindDirectives = false;

    /// Constructs a new set of parser metadata by walking the provided syntax tree.
    static ParserMetadata fromSyntax(const syntax::SyntaxNode& root);
};

} // namespace slang::parsing
