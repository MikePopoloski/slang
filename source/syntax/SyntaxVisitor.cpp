//------------------------------------------------------------------------------
// SyntaxVisitor.cpp
// Syntax tree visitor support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxVisitor.h"

#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"

namespace {

using namespace slang;
using namespace slang::syntax;
using namespace slang::syntax::detail;
using slang::parsing::ParserMetadata;

struct RemoveVisitor : SyntaxVisitor<RemoveVisitor> {
    ParserMetadata& metadata;
    RemoveVisitor(ParserMetadata& metadata) : metadata(metadata) {}
    void handle(const ModuleDeclarationSyntax& oldNode) { metadata.nodeMap.erase(&oldNode); }
    void handle(const IdentifierNameSyntax& oldNode) {
        auto it = std::find(begin(metadata.classPackageNames), end(metadata.classPackageNames),
                            &oldNode);
        if (it != end(metadata.classPackageNames))
            metadata.classPackageNames.erase(it);
    }
    void handle(const PackageImportDeclarationSyntax& oldNode) {
        auto it = std::find(begin(metadata.packageImports), end(metadata.packageImports), &oldNode);
        if (it != end(metadata.packageImports))
            metadata.packageImports.erase(it);
    }
    void handle(const DefParamSyntax& oldNode) {
        auto it = std::find(begin(metadata.defparams), end(metadata.defparams), &oldNode);
        if (it != end(metadata.defparams))
            metadata.defparams.erase(it);
    }
    void handle(const ClassDeclarationSyntax& oldNode) {
        auto it = std::find(begin(metadata.classDecls), end(metadata.classDecls), &oldNode);
        if (it != end(metadata.classDecls))
            metadata.classDecls.erase(it);
    }
    void handle(const BindDirectiveSyntax& oldNode) {
        auto it = std::find(begin(metadata.bindDirectives), end(metadata.bindDirectives), &oldNode);
        if (it != end(metadata.bindDirectives))
            metadata.bindDirectives.erase(it);
    }
};

struct InsertVisitor : SyntaxVisitor<InsertVisitor> {
    ParserMetadata& metadata;
    SyntaxTree& originTree;

    InsertVisitor(ParserMetadata& metadata, SyntaxTree& tree) :
        metadata(metadata), originTree(tree) {}

    void handle(const ModuleDeclarationSyntax& newNode) {
        // Special Case, need to reparse the new module again

        BumpAllocator alloc;
        Diagnostics diagnostics;
        parsing::Preprocessor preprocessor(originTree.sourceManager(), alloc, diagnostics,
                                           originTree.options(), originTree.getDefinedMacros());

        parsing::Parser parser(preprocessor);
        preprocessor.pushSource(newNode.toString());

        parser.parseGuess();
        if (parser.isDone()) {
            ParserMetadata::Node node{preprocessor.getDefaultNetType(),
                                      preprocessor.getUnconnectedDrive(),
                                      preprocessor.getTimeScale()};
            metadata.nodeMap[&newNode] = std::move(node);
        }
    }

    void handle(const IdentifierNameSyntax& newNode) {
        metadata.classPackageNames.push_back(&newNode);
    }
    void handle(const PackageImportDeclarationSyntax& newNode) {
        metadata.packageImports.push_back(&newNode);
    }
    void handle(const DefParamSyntax& newNode) { metadata.defparams.push_back(&newNode); }
    void handle(const ClassDeclarationSyntax& newNode) { metadata.classDecls.push_back(&newNode); }
    void handle(const BindDirectiveSyntax& newNode) { metadata.bindDirectives.push_back(&newNode); }
};

struct CloneVisitor {
    BumpAllocator& alloc;
    const ChangeCollection& commits;
    ParserMetadata& metadata;
    SyntaxTree& originTree;

    CloneVisitor(BumpAllocator& alloc, const ChangeCollection& commits, ParserMetadata& metadata,
                 SyntaxTree& tree) :
        alloc(alloc),
        commits(commits), metadata(metadata), originTree(tree) {}

    void remove(const SyntaxNode* oldChild) {
        RemoveVisitor visitor(metadata);
        oldChild->visit(visitor);
    }

    void insert(const SyntaxNode* newChild) {
        InsertVisitor visitor(metadata, originTree);
        newChild->visit(visitor);
    }

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4127) // conditional expression is constant
#endif
    template<typename T>
    SyntaxNode* visit(const T& node) {
        T* cloned = node.clone(alloc);

        constexpr bool IsList = std::is_same_v<T, SyntaxListBase>;
        SmallVectorSized<TokenOrSyntax, 8> listBuffer;

        if constexpr (IsList) {
            if (auto it = commits.listInsertAtFront.find(&node);
                it != commits.listInsertAtFront.end()) {

                const SyntaxChange* lastChange = nullptr;
                for (const auto& change : it->second) {
                    if (!listBuffer.empty() && change.separator)
                        listBuffer.append(change.separator);
                    listBuffer.append(change.second);
                    lastChange = &change;
                }

                if (lastChange && node.getChildCount() && lastChange->separator)
                    listBuffer.append(lastChange->separator);
            }
        }

        for (size_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (!child) {
                if constexpr (IsList)
                    listBuffer.append(node.childToken(i));
                continue;
            }

            if (auto it = commits.insertBefore.find(child); it != commits.insertBefore.end()) {
                if (!IsList) {
                    throw std::logic_error(
                        "Can't use insertBefore or insertAfter on a non-list node");
                }

                for (const auto& change : it->second) {
                    listBuffer.append(change.second);
                    insert(change.second);
                }
            }

            if (auto it = commits.removeOrReplace.find(child);
                it != commits.removeOrReplace.end()) {
                remove(child);
                if (auto replaceChange = std::get_if<ReplaceChange>(&it->second)) {
                    if constexpr (IsList)
                        listBuffer.append(replaceChange->second);
                    else
                        cloned->setChild(i, replaceChange->second);

                    insert(replaceChange->second);
                }
            }
            else {
                if constexpr (IsList) {
                    listBuffer.append(child->visit(*this));
                }
                else {
                    cloned->setChild(i, child->visit(*this));
                }
            }

            if (auto it = commits.insertAfter.find(child); it != commits.insertAfter.end()) {
                if (!IsList) {
                    throw std::logic_error(
                        "Can't use insertBefore or insertAfter on a non-list node");
                }

                for (const auto& change : it->second) {
                    listBuffer.append(change.second);
                    insert(change.second);
                }
            }
        }

        if constexpr (IsList) {
            if (auto it = commits.listInsertAtBack.find(&node);
                it != commits.listInsertAtBack.end()) {

                for (const auto& change : it->second) {
                    if (!listBuffer.empty() && change.separator)
                        listBuffer.append(change.separator);
                    listBuffer.append(change.second);
                }
            }

            cloned->resetAll(alloc, listBuffer);
        }

        return cloned;
    }
#ifdef _MSC_VER
#    pragma warning(pop)
#endif

    SyntaxNode* visitInvalid(const SyntaxNode&) {
        ASSUME_UNREACHABLE;
    }
};

} // namespace

namespace slang::syntax::detail {

std::shared_ptr<SyntaxTree> transformTree(
    BumpAllocator&& alloc, const std::shared_ptr<SyntaxTree>& tree, const ChangeCollection& commits,
    const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees) {

    auto metadata = tree ? std::make_unique<ParserMetadata>(tree->getMetadata())
                         : std::make_unique<ParserMetadata>();

    CloneVisitor visitor(alloc, commits, *metadata, *tree);

    SyntaxNode* root = tree->root().visit(visitor);

    // Steal ownership of any temporary syntax trees that the user created; once we return the
    // user expects that the newly transformed tree fully owns all of its memory.
    for (auto& t : tempTrees)
        alloc.steal(std::move(t->allocator()));

    return std::make_shared<SyntaxTree>(root, tree->sourceManager(), std::move(alloc),
                                        std::move(metadata), tree);
}

} // namespace slang::syntax::detail
