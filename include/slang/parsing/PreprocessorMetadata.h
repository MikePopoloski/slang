//------------------------------------------------------------------------------
//! @file PreprocessorMetadata.h
//! @brief Metadata collected during preprocessing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string_view>
#include <vector>

#include "slang/syntax/SyntaxFwd.h"
#include "slang/text/SourceLocation.h"

namespace slang::parsing {

/// Metadata about an include directive that was invoked.
struct SLANG_EXPORT IncludeMetadata {
    const syntax::IncludeDirectiveSyntax* syntax;
    std::string_view path;
    SourceBuffer buffer;
    bool isSystem;
};

/// Metadata about a macro reference (usage or undef) and its active definition.
struct SLANG_EXPORT MacroRefMetadata {
    /// The syntax node referencing the macro (MacroUsage or UndefDirective)
    const syntax::SyntaxNode* syntax;
    /// The macro definition that was used for the expansion
    const syntax::DefineDirectiveSyntax* definition;
};

/// Various bits of metadata collected during preprocessing.
struct SLANG_EXPORT PreprocessorMetadata {
    /// The macros that were defined at the end of preprocessing.
    std::vector<const syntax::DefineDirectiveSyntax*> definedMacros;

    /// The include directives that were encountered while preprocessing.
    std::vector<IncludeMetadata> includeDirectives;

    /// The macro references that were expanded while preprocessing.
    std::vector<MacroRefMetadata> macroRefs;

    /// The source buffer IDs that were pushed into the preprocessor, in order.
    /// This includes top-level and included source files, but not macro expansion buffers.
    std::vector<BufferID> sourceBufferIds;
};

} // namespace slang::parsing
