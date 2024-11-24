//------------------------------------------------------------------------------
//! @file SyntaxTree.h
//! @brief Top-level parser interface
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <expected.hpp>
#include <memory>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/parsing/ParserMetadata.h"
#include "slang/util/Bag.h"
#include "slang/util/BumpAllocator.h"

namespace slang {

class SourceManager;
struct SourceBuffer;

} // namespace slang

namespace slang::parsing {
struct ParserMetadata;
}

namespace slang::syntax {

class SyntaxNode;
struct DefineDirectiveSyntax;

/// The SyntaxTree is the easiest way to interface with the lexer / preprocessor /
/// parser stack. Give it some source text and it produces a parse tree.
///
/// The SyntaxTree object owns all of the memory for the parse tree, so it must
/// live for as long as you need to access its syntax nodes.
class SLANG_EXPORT SyntaxTree {
public:
    using TreeOrError =
        nonstd::expected<std::shared_ptr<SyntaxTree>, std::pair<std::error_code, std::string_view>>;
    using MacroList = std::span<const DefineDirectiveSyntax* const>;

    /// Indicates whether this syntax tree represents a "library" compilation unit,
    /// which means that modules declared within it are not automatically instantiated.
    bool isLibraryUnit = false;

    SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
               const SourceLibrary* library, const std::shared_ptr<SyntaxTree>& parent = nullptr);

    SyntaxTree(SyntaxTree&& other) = default;
    ~SyntaxTree();

    /// Creates a syntax tree from a full compilation unit.
    /// @a path is the path to the source file on disk.
    /// @return the created and parsed syntax tree.
    static TreeOrError fromFile(std::string_view path);

    /// Creates a syntax tree from a full compilation unit.
    /// @a path is the path to the source file on disk.
    /// @a sourceManager is the manager that owns all of the loaded source code.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree on success, or an OS error
    ///         code if the file fails to load.
    static TreeOrError fromFile(std::string_view path, SourceManager& sourceManager,
                                const Bag& options = {});

    /// Creates a syntax tree by concatenating several files loaded from disk.
    /// @a paths is the list of paths to the source files on disk.
    /// @return the created and parsed syntax tree on success, or an OS error
    ///         code if the file fails to load.
    static TreeOrError fromFiles(std::span<const std::string_view> paths);

    /// Creates a syntax tree by concatenating several files loaded from disk.
    /// @a paths is the list of paths to the source files on disk.
    /// @a sourceManager is the manager that owns all of the loaded source code.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree on success, or an OS error
    ///         code if the file fails to load.
    static TreeOrError fromFiles(std::span<const std::string_view> paths,
                                 SourceManager& sourceManager, const Bag& options = {});

    /// Creates a syntax tree by guessing at what might be in the given source snippet.
    /// @a text is the actual source code text.
    /// @a name is an optional name to give to the loaded source buffer.
    /// @a path is an optional path to give to the loaded source buffer.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromText(std::string_view text,
                                                std::string_view name = "source",
                                                std::string_view path = "");

    /// Creates a syntax tree by guessing at what might be in the given source snippet.
    /// @a text is the actual source code text.
    /// @a options is a bag of lexer, preprocessor, and parser options.
    /// @a name is an optional name to give to the loaded source buffer.
    /// @a path is an optional path to give to the loaded source buffer.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromText(std::string_view text, const Bag& options,
                                                std::string_view name = "source"sv,
                                                std::string_view path = "");

    /// Creates a syntax tree by guessing at what might be in the given source snippet.
    /// @a text is the actual source code text.
    /// @a sourceManager is the manager that owns all of the loaded source code.
    /// @a name is an optional name to give to the loaded source buffer.
    /// @a path is an optional path to give to the loaded source buffer.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @a library the source library to associated with the parsed tree
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromText(std::string_view text, SourceManager& sourceManager,
                                                std::string_view name = "source"sv,
                                                std::string_view path = "", const Bag& options = {},
                                                const SourceLibrary* library = nullptr);

    /// Creates a syntax tree from a full compilation unit already in memory.
    /// @a text is the actual source code text.
    /// @a sourceManager is the manager that owns all of the loaded source code.
    /// @a name is an optional name to give to the loaded source buffer.
    /// @a path is an optional path to give to the loaded source buffer.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromFileInMemory(std::string_view text,
                                                        SourceManager& sourceManager,
                                                        std::string_view name = "source"sv,
                                                        std::string_view path = "",
                                                        const Bag& options = {});

    /// Creates a syntax tree from an already loaded source buffer.
    /// @a buffer is the loaded source buffer.
    /// @a sourceManager is the manager that owns the buffer.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @a inheritedMacros is a list of macros to predefine in the new syntax tree.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromBuffer(const SourceBuffer& buffer,
                                                  SourceManager& sourceManager,
                                                  const Bag& options = {},
                                                  MacroList inheritedMacros = {});

    /// Creates a syntax tree by concatenating several loaded source buffers.
    /// @a buffers is the list of buffers that should be concatenated to form
    /// the compilation unit to parse.
    /// @a sourceManager is the manager that owns the buffers.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @a inheritedMacros is a list of macros to predefine in the new syntax tree.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromBuffers(std::span<const SourceBuffer> buffers,
                                                   SourceManager& sourceManager,
                                                   const Bag& options = {},
                                                   MacroList inheritedMacros = {});

    /// Creates a syntax tree from a library map file.
    /// @a path is the path to the source file on disk.
    /// @a sourceManager is the manager that owns all of the loaded source code.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromLibraryMapFile(std::string_view path,
                                                          SourceManager& sourceManager,
                                                          const Bag& options = {});

    /// Creates a syntax tree from a library map located in memory.
    /// @a text is the actual source code text.
    /// @a sourceManager is the manager that owns all of the loaded source code.
    /// @a name is an optional name to give to the loaded source buffer.
    /// @a path is an optional path to give to the loaded source buffer.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromLibraryMapText(std::string_view text,
                                                          SourceManager& sourceManager,
                                                          std::string_view name = "source"sv,
                                                          std::string_view path = "",
                                                          const Bag& options = {});

    /// Creates a syntax tree from a library map already loaded into a source buffer.
    /// @a buffer is the loaded source buffer.
    /// @a sourceManager is the manager that owns the buffer.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromLibraryMapBuffer(const SourceBuffer& buffer,
                                                            SourceManager& sourceManager,
                                                            const Bag& options = {});

    /// Gets any diagnostics generated while parsing.
    Diagnostics& diagnostics() { return diagnosticsBuffer; }

    /// Gets the allocator containing the memory for the parse tree.
    BumpAllocator& allocator() { return alloc; }

    /// Gets the source manager used to build the syntax tree.
    SourceManager& sourceManager() { return sourceMan; }

    /// Gets the source manager used to build the syntax tree.
    const SourceManager& sourceManager() const { return sourceMan; }

    /// Gets the source library with which the syntax tree is associated.
    const SourceLibrary* getSourceLibrary() const { return library; }

    /// Gets the root of the syntax tree.
    SyntaxNode& root() { return *rootNode; }

    /// Gets the root of the syntax tree.
    const SyntaxNode& root() const { return *rootNode; }

    /// The options used to construct the syntax tree.
    const Bag& options() const { return options_; }

    /// Gets various bits of metadata collected during parsing.
    const parsing::ParserMetadata& getMetadata() const { return *metadata; }

    /// Gets the list of macros that were defined at the end of the loaded source file.
    MacroList getDefinedMacros() const { return macros; }

    /// This is a shared default source manager for cases where the user doesn't
    /// care about managing the lifetime of loaded source. Note that all of
    /// the source loaded by this thing will live in memory for the lifetime of
    /// the process.
    static SourceManager& getDefaultSourceManager();

private:
    SyntaxTree(SyntaxNode* root, const SourceLibrary* library, SourceManager& sourceManager,
               BumpAllocator&& alloc, Diagnostics&& diagnostics, parsing::ParserMetadata&& metadata,
               std::vector<const DefineDirectiveSyntax*>&& macros, Bag options);

    static std::shared_ptr<SyntaxTree> create(SourceManager& sourceManager,
                                              std::span<const SourceBuffer> source,
                                              const Bag& options, MacroList inheritedMacros,
                                              bool guess);

    SyntaxNode* rootNode;
    const SourceLibrary* library;
    SourceManager& sourceMan;
    BumpAllocator alloc;
    Diagnostics diagnosticsBuffer;
    Bag options_;
    std::unique_ptr<parsing::ParserMetadata> metadata;
    std::vector<const DefineDirectiveSyntax*> macros;
};

} // namespace slang::syntax
