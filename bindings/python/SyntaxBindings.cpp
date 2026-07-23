//------------------------------------------------------------------------------
// SyntaxBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "PyVisitors.h"
#include "pyslang.h"

#include "slang/parsing/Lexer.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/CSTSerializer.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxRewriter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/Json.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"

namespace fs = std::filesystem;

namespace {

struct PySyntaxVisitor
    : public PyVisitorBase<PySyntaxVisitor, std::tuple<SyntaxKind, parsing::TokenKind>,
                           SyntaxVisitor> {
    using PyVisitorBase::PyVisitorBase;

    template<typename T>
    void handle(const T& t) {
        if (this->interrupted)
            return;

        // Note: the cast to SyntaxNode here is very important.
        // It means that the object Python sees is of type SyntaxNode,
        // forcing them to go through the polymorphic downcaster to get
        // at the actual type.
        auto node = static_cast<const SyntaxNode*>(&t);

        nb::object result;
        if (this->lookupTable) {
            nb::handle handler = this->tables.find(t.kind);
            if (handler)
                result = handler(node);
        }
        else {
            result = this->f(node);
        }

        if (this->applyResult(result))
            this->visitDefault(t);
    }

    void visitToken(parsing::Token t) {
        if (this->interrupted)
            return;

        nb::object result;
        if (this->lookupTable) {
            nb::handle handler = this->tables.find(t.kind);
            if (handler)
                result = handler(t);
        }
        else {
            result = this->f(t);
        }

        // Tokens are leaves; applyResult records an Interrupt and Skip is a no-op here.
        this->applyResult(result);
    }
};

void pySyntaxVisit(const SyntaxNode& sn, nb::object f = nb::none(),
                   nb::object lookup_table = nb::none()) {
    if (f.is_none() && lookup_table.is_none())
        throw nb::type_error("visit() requires 'f' or 'lookup_table' (both are None)");

    std::optional<nb::dict> lt;
    if (!lookup_table.is_none())
        lt = nb::cast<nb::dict>(lookup_table);

    PySyntaxVisitor visitor{f, std::move(lt)};
    sn.visit(visitor);
}

class PySyntaxRewriter : public SyntaxRewriter<PySyntaxRewriter> {
public:
    PySyntaxRewriter(nb::object handler) : handler(std::move(handler)) {}

    void visit(const SyntaxNode& node) {
        try {
            handler(nb::cast(&node), nb::cast(this));
        }
        catch (const nb::python_error& e) {
            throw;
        }
        visitDefault(node);
    }

    // --- Expose protected base methods via public wrappers ---
    void py_remove(const SyntaxNode& node) { this->remove(node); }

    void py_replace(const SyntaxNode& oldNode, SyntaxNode& newNode, bool preserveTrivia = false) {
        this->replace(oldNode, cloneNode(newNode), preserveTrivia);
    }

    void py_insertBefore(const SyntaxNode& node, SyntaxNode& newNode) {
        this->insertBefore(node, cloneNode(newNode));
    }

    void py_insertAfter(const SyntaxNode& node, SyntaxNode& newNode) {
        this->insertAfter(node, cloneNode(newNode));
    }

    template<typename TList>
        requires is_syntax_list_v<TList>
    void py_insertAtFront(const TList& list, SyntaxNode& newNode, Token separator = {}) {
        this->insertAtFront(list, cloneNode(newNode), separator);
    }

    template<typename TList>
        requires is_syntax_list_v<TList>
    void py_insertAtBack(const TList& list, SyntaxNode& newNode, Token separator = {}) {
        this->insertAtBack(list, cloneNode(newNode), separator);
    }

    SyntaxFactory& getFactory() { return factory; }

    BumpAllocator& getAllocator() { return alloc; }

    Token py_makeToken(TokenKind kind, std::string_view text, std::span<const Trivia> trivia = {}) {
        return this->makeToken(kind, toStringView(alloc.copyFrom(std::span(text))),
                               alloc.copyFrom(trivia));
    }

    Token py_makeTokenFromKind(TokenKind kind, std::span<const Trivia> trivia = {}) {
        auto text = LexerFacts::getTokenKindText(kind);
        if (text.empty()) {
            throw std::invalid_argument(
                "TokenKind requires explicit text (use makeToken(kind, text) instead)");
        }
        auto persistentTrivia = alloc.copyFrom(trivia);
        return this->makeToken(kind, text, persistentTrivia);
    }

    Token py_makeId(std::string_view text, std::span<const Trivia> trivia = {}) {
        return this->makeId(toStringView(alloc.copyFrom(std::span(text))), alloc.copyFrom(trivia));
    }

    Token py_makeComma() { return this->makeComma(); }

    Trivia py_makeTrivia(TriviaKind kind, std::string_view text) {
        return Trivia(kind, toStringView(alloc.copyFrom(std::span(text))));
    }

    SyntaxNode* py_clone(const SyntaxNode& node) { return clone(node, this->alloc); }

    SyntaxNode* py_deepClone(const SyntaxNode& node) { return deepClone(node, this->alloc); }

    template<typename T>
    SyntaxList<T>& py_makeSyntaxList(nb::list items) {
        SmallVector<T*> buffer;
        for (auto item : items) {
            buffer.push_back(&cloneNode(nb::cast<T&>(item)));
        }
        return *alloc.emplace<SyntaxList<T>>(alloc, buffer);
    }

    SyntaxList<SyntaxNode>& py_makeSyntaxListGeneric(nb::list items) {
        return py_makeSyntaxList<SyntaxNode>(items);
    }

    template<typename T>
    SeparatedSyntaxList<T>& py_makeSeparatedSyntaxList(nb::list items) {
        SmallVector<TokenOrSyntax> buffer;
        for (size_t i = 0; i < nb::len(items); i++) {
            nb::object item = items[i];
            if (nb::isinstance<Token>(item)) {
                buffer.push_back(nb::cast<Token>(item));
            }
            else {
                buffer.push_back(&cloneNode(nb::cast<SyntaxNode&>(item)));
            }
        }
        return *alloc.emplace<SeparatedSyntaxList<T>>(alloc, buffer);
    }

    SeparatedSyntaxList<SyntaxNode>& py_makeSeparatedSyntaxListGeneric(nb::list items) {
        return py_makeSeparatedSyntaxList<SyntaxNode>(items);
    }

    TokenList& py_makeTokenList(nb::list items) {
        SmallVector<Token> buffer;
        for (auto item : items) {
            buffer.push_back(nb::cast<Token>(item));
        }
        return *alloc.emplace<TokenList>(alloc, buffer);
    }

private:
    nb::object handler;

    SyntaxNode& cloneNode(const SyntaxNode& node) { return *deepClone(node, this->alloc); }
};

std::shared_ptr<SyntaxTree> pySyntaxRewrite(const std::shared_ptr<SyntaxTree>& tree,
                                            nb::object handler) {
    PySyntaxRewriter rewriter(std::move(handler));
    return rewriter.transform(tree);
}

} // end namespace

void registerSyntax(nb::module_& syntax, nb::module_& parsing) {
    auto& m = syntax;
    EXPOSE_ENUM(parsing, TriviaKind);
    EXPOSE_ENUM(parsing, TokenKind);
    EXPOSE_ENUM(m, SyntaxKind);
    EXPOSE_ENUM(parsing, KnownSystemName);
    EXPOSE_ENUM(m, CSTJsonMode);

    nb::class_<Trivia>(parsing, "Trivia")
        .def(nb::init<>())
        .def(nb::init<TriviaKind, std::string_view>(), "kind"_a, "rawText"_a)
        .def_ro("kind", &Trivia::kind)
        .def("getExplicitLocation", &Trivia::getExplicitLocation)
        .def("syntax", &Trivia::syntax, byrefint)
        .def("getRawText", &Trivia::getRawText)
        .def("getSkippedTokens", &Trivia::getSkippedTokens)
        .def("__repr__", [](const Trivia& self) {
            return fmt::format("Trivia(TriviaKind.{})", toString(self.kind));
        });

    nb::class_<Token>(parsing, "Token")
        .def(nb::init<>())
        .def(
            "__init__",
            [](Token* self, BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
               std::string_view rawText, SourceLocation location) {
                new (self) Token(alloc, kind, alloc.copyFrom(trivia), rawText, location);
            },
            nb::keep_alive<1, 2>(), nb::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
            "rawText"_a, "location"_a)
        .def(
            "__init__",
            [](Token* self, BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
               std::string_view rawText, SourceLocation location, std::string_view strText) {
                new (self) Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, strText);
            },
            nb::keep_alive<1, 2>(), nb::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
            "rawText"_a, "location"_a, "strText"_a)
        .def(
            "__init__",
            [](Token* self, BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
               std::string_view rawText, SourceLocation location, SyntaxKind directive) {
                new (self) Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, directive);
            },
            nb::keep_alive<1, 2>(), nb::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
            "rawText"_a, "location"_a, "directive"_a)
        .def(
            "__init__",
            [](Token* self, BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
               std::string_view rawText, SourceLocation location, logic_t bit) {
                new (self) Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, bit);
            },
            nb::keep_alive<1, 2>(), nb::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
            "rawText"_a, "location"_a, "bit"_a)
        .def(
            "__init__",
            [](Token* self, BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
               std::string_view rawText, SourceLocation location, const SVInt& value) {
                new (self) Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, value);
            },
            nb::keep_alive<1, 2>(), nb::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
            "rawText"_a, "location"_a, "value"_a)
        .def(
            "__init__",
            [](Token* self, BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
               std::string_view rawText, SourceLocation location, double realValue, bool outOfRange,
               std::optional<TimeUnit> timeUnit) {
                new (self) Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, realValue,
                                 outOfRange, timeUnit);
            },
            nb::keep_alive<1, 2>(), nb::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
            "rawText"_a, "location"_a, "value"_a, "outOfRange"_a, "timeUnit"_a)
        .def(
            "__init__",
            [](Token* self, BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
               std::string_view rawText, SourceLocation location, LiteralBase base, bool isSigned) {
                new (self)
                    Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, base, isSigned);
            },
            nb::keep_alive<1, 2>(), nb::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
            "rawText"_a, "location"_a, "base"_a, "isSigned"_a)
        .def_ro("kind", &Token::kind)
        .def_prop_ro("isMissing", &Token::isMissing)
        .def_prop_ro("range", &Token::range)
        .def_prop_ro("location", &Token::location)
        .def_prop_ro("trivia",
                     [](const Token& t) {
                         auto view = t.trivia();
                         return std::vector<Trivia>(view.begin(), view.end());
                     })
        .def_prop_ro("valueText", &Token::valueText)
        .def_prop_ro("rawText", &Token::rawText)
        .def_prop_ro("isOnSameLine", &Token::isOnSameLine)
        .def_prop_ro("value",
                     [](const Token& t) -> nb::object {
                         switch (t.kind) {
                             case TokenKind::IntegerLiteral:
                                 return nb::cast(t.intValue());
                             case TokenKind::RealLiteral:
                             case TokenKind::TimeLiteral:
                                 return nb::cast(t.realValue());
                             case TokenKind::UnbasedUnsizedLiteral:
                                 return nb::cast(t.bitValue());
                             case TokenKind::StringLiteral:
                             case TokenKind::Identifier:
                                 return nb::cast(t.valueText());
                             default:
                                 return nb::none();
                         }
                     })
        .def(nb::self == nb::self)
        .def(nb::self != nb::self)
        .def("__bool__", &Token::operator bool)
        .def("__repr__",
             [](const Token& self) {
                 return fmt::format("Token(TokenKind.{})", toString(self.kind));
             })
        .def("__str__", &Token::toString);

    class SyntaxNodeIterator : public iterator_facade<SyntaxNodeIterator> {
    public:
        SyntaxNodeIterator() : node(nullptr), index(0) {}
        SyntaxNodeIterator(const SyntaxNode& node, size_t index) : node(&node), index(index) {
            skipToNext();
        }

        nb::object dereference() const {
            if (auto child = node->childNode(index))
                return nb::cast(child, byrefint, nb::cast(node));
            return nb::cast(node->childToken(index));
        }

        bool equals(const SyntaxNodeIterator& other) const {
            return node == other.node && index == other.index;
        }

        void increment() {
            index++;
            skipToNext();
        }

    private:
        void skipToNext() {
            while (index < node->getChildCount() && !node->childNode(index) &&
                   !node->childToken(index)) {
                index++;
            }
        }

        const SyntaxNode* node;
        size_t index;
    };

    nb::class_<SyntaxNode>(m, "SyntaxNode")
        .def_prop_ro(
            "parent", [](const SyntaxNode& n) -> const SyntaxNode* { return n.parent; }, byrefint)
        .def_ro("kind", &SyntaxNode::kind)
        .def("getFirstToken", &SyntaxNode::getFirstToken)
        .def("getLastToken", &SyntaxNode::getLastToken)
        .def("isEquivalentTo", &SyntaxNode::isEquivalentTo, "other"_a)
        .def("visit", &pySyntaxVisit, "f"_a = nb::none(), "lookup_table"_a = nb::none(),
             PySyntaxVisitor::doc)
        .def_prop_ro("sourceRange", &SyntaxNode::sourceRange)
        .def("__getitem__",
             [](const SyntaxNode& self, size_t i) -> nb::object {
                 if (i >= self.getChildCount())
                     throw nb::index_error();

                 if (auto node = self.childNode(i))
                     return nb::cast(node, byrefint, nb::cast(&self));

                 if (auto token = self.childToken(i))
                     return nb::cast(self.childToken(i));

                 return nb::none();
             })
        .def("__len__", &SyntaxNode::getChildCount)
        .def(
            "__iter__",
            [](const SyntaxNode& s) {
                return nb::make_iterator(nb::type<SyntaxNode>(), "SyntaxNodeIterator",
                                         SyntaxNodeIterator(s, 0),
                                         SyntaxNodeIterator(s, s.getChildCount()));
            },
            nb::keep_alive<0, 1>())
        .def("__repr__",
             [](const SyntaxNode& self) {
                 return fmt::format("SyntaxNode(SyntaxKind.{})", toString(self.kind));
             })
        .def("__str__", &SyntaxNode::toString)
        .def(
            "to_json",
            [](const SyntaxNode& self, CSTJsonMode mode = CSTJsonMode::Full) {
                JsonWriter writer;
                writer.setPrettyPrint(true);
                CSTSerializer serializer(writer, mode);
                serializer.serialize(self);
                return std::string(writer.view());
            },
            "mode"_a = CSTJsonMode::Full,
            "Convert this syntax node to JSON string with optional formatting "
            "mode");

    nb::class_<IncludeMetadata>(m, "IncludeMetadata")
        .def(nb::init<>())
        .def_ro("syntax", &IncludeMetadata::syntax)
        .def_ro("path", &IncludeMetadata::path)
        .def_ro("buffer", &IncludeMetadata::buffer)
        .def_ro("isSystem", &IncludeMetadata::isSystem);

    nb::class_<SyntaxTree>(m, "SyntaxTree")
        .def_ro("isLibraryUnit", &SyntaxTree::isLibraryUnit)
        .def_static(
            "fromFile",
            [](std::string_view path) {
                auto result = SyntaxTree::fromFile(path);
                if (!result)
                    throw fs::filesystem_error("", path, result.error().first);
                return *result;
            },
            "path"_a)
        .def_static(
            "fromFile",
            [](std::string_view path, SourceManager& sourceManager, const Bag& options) {
                auto result = SyntaxTree::fromFile(path, sourceManager, options);
                if (!result)
                    throw fs::filesystem_error("", path, result.error().first);
                return *result;
            },
            nb::keep_alive<0, 2>(), "path"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static(
            "fromFiles",
            [](std::span<const std::string_view> paths) {
                auto result = SyntaxTree::fromFiles(paths);
                if (!result)
                    throw fs::filesystem_error("", result.error().second, result.error().first);
                return *result;
            },
            "paths"_a)
        .def_static(
            "fromFiles",
            [](std::span<const std::string_view> paths, SourceManager& sourceManager,
               const Bag& options) {
                auto result = SyntaxTree::fromFiles(paths, sourceManager, options);
                if (!result)
                    throw fs::filesystem_error("", result.error().second, result.error().first);
                return *result;
            },
            nb::keep_alive<0, 2>(), "paths"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static("fromText",
                    nb::overload_cast<std::string_view, std::string_view, std::string_view>(
                        &SyntaxTree::fromText),
                    "text"_a, "name"_a = "source", "path"_a = "")
        .def_static("fromText",
                    nb::overload_cast<std::string_view, SourceManager&, std::string_view,
                                      std::string_view, const Bag&, const SourceLibrary*>(
                        &SyntaxTree::fromText),
                    nb::keep_alive<0, 2>(), "text"_a, "sourceManager"_a, "name"_a = "source",
                    "path"_a = "", "options"_a = Bag(), "library"_a = nullptr)
        .def_static("fromFileInMemory", &SyntaxTree::fromFileInMemory, nb::keep_alive<0, 2>(),
                    "text"_a, "sourceManager"_a, "name"_a = "source", "path"_a = "",
                    "options"_a = Bag())
        .def_static("fromBuffer", &SyntaxTree::fromBuffer, nb::keep_alive<0, 2>(), "buffer"_a,
                    "sourceManager"_a, "options"_a = Bag(),
                    "inheritedMacros"_a = SyntaxTree::MacroList{})
        .def_static("fromBuffers", &SyntaxTree::fromBuffers, nb::keep_alive<0, 2>(), "buffers"_a,
                    "sourceManager"_a, "options"_a = Bag(),
                    "inheritedMacros"_a = SyntaxTree::MacroList{})
        .def_static("fromLibraryMapFile", &SyntaxTree::fromLibraryMapFile, nb::keep_alive<0, 2>(),
                    "path"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static("fromLibraryMapText", &SyntaxTree::fromLibraryMapText, nb::keep_alive<0, 2>(),
                    "text"_a, "sourceManager"_a, "name"_a = "source", "path"_a = "",
                    "options"_a = Bag())
        .def_static("fromLibraryMapBuffer", &SyntaxTree::fromLibraryMapBuffer,
                    nb::keep_alive<0, 2>(), "buffer"_a, "sourceManager"_a, "options"_a = Bag())
        .def_prop_ro("diagnostics", &SyntaxTree::diagnostics)
        .def_prop_ro("sourceManager", nb::overload_cast<>(&SyntaxTree::sourceManager))
        .def_prop_ro("root", nb::overload_cast<>(&SyntaxTree::root), byrefint)
        .def_prop_ro("options", &SyntaxTree::options)
        .def_prop_ro("sourceLibrary", &SyntaxTree::getSourceLibrary)
        .def("getIncludeDirectives", &SyntaxTree::getIncludeDirectives)
        .def_static("getDefaultSourceManager", &SyntaxTree::getDefaultSourceManager, byref)
        .def("validate", &SyntaxTree::validate)
        .def(
            "to_json",
            [](const SyntaxTree& self, CSTJsonMode mode = CSTJsonMode::Full) {
                JsonWriter writer;
                writer.setPrettyPrint(true);
                CSTSerializer serializer(writer, mode);
                serializer.serialize(self);
                return std::string(writer.view());
            },
            "mode"_a = CSTJsonMode::Full,
            "Convert this syntax tree to JSON string with optional formatting "
            "mode");

    nb::class_<CommentHandler> commentHandler(m, "CommentHandler");
    commentHandler.def(nb::init<>())
        .def(nb::init<CommentHandler::Kind, std::string_view>(), "kind"_a, "endRegion"_a)
        .def_rw("kind", &CommentHandler::kind)
        .def_rw("endRegion", &CommentHandler::endRegion);

    nb::enum_<CommentHandler::Kind>(commentHandler, "Kind")
        .value("Protect", CommentHandler::Protect)
        .value("TranslateOff", CommentHandler::TranslateOff)
        .value("LintOn", CommentHandler::LintOn)
        .value("LintOff", CommentHandler::LintOff)
        .value("LintSave", CommentHandler::LintSave)
        .value("LintRestore", CommentHandler::LintRestore)
        .export_values();

    nb::class_<LexerOptions>(parsing, "LexerOptions")
        .def(nb::init<>())
        .def_rw("maxErrors", &LexerOptions::maxErrors)
        .def_rw("languageVersion", &LexerOptions::languageVersion)
        .def_rw("enableLegacyProtect", &LexerOptions::enableLegacyProtect)
        .def_rw("commentHandlers", &LexerOptions::commentHandlers);

    nb::class_<Lexer>(parsing, "Lexer")
        .def(nb::init<SourceBuffer, BumpAllocator&, Diagnostics&, SourceManager&, LexerOptions>(),
             nb::keep_alive<1, 3>(), nb::keep_alive<1, 4>(), nb::keep_alive<1, 5>(), "buffer"_a,
             "alloc"_a, "diagnostics"_a, "sourceManager"_a, "options"_a = LexerOptions())
        .def("lex", nb::overload_cast<>(&Lexer::lex))
        .def("isNextTokenOnSameLine", &Lexer::isNextTokenOnSameLine)
        .def_prop_ro("library", &Lexer::getLibrary)
        .def_prop_ro("bufferId", &Lexer::getBufferId);

    nb::class_<PreprocessorOptions>(parsing, "PreprocessorOptions")
        .def(nb::init<>())
        .def_rw("maxIncludeDepth", &PreprocessorOptions::maxIncludeDepth)
        .def_rw("languageVersion", &PreprocessorOptions::languageVersion)
        .def_rw("predefineSource", &PreprocessorOptions::predefineSource)
        .def_rw("predefines", &PreprocessorOptions::predefines)
        .def_rw("undefines", &PreprocessorOptions::undefines)
        .def_rw("additionalIncludePaths", &PreprocessorOptions::additionalIncludePaths)
        .def_rw("ignoreDirectives", &PreprocessorOptions::ignoreDirectives)
        .def_rw("keywordMapping", &PreprocessorOptions::keywordMapping);

    nb::class_<ParserOptions>(parsing, "ParserOptions")
        .def(nb::init<>())
        .def_rw("maxRecursionDepth", &ParserOptions::maxRecursionDepth)
        .def_rw("languageVersion", &ParserOptions::languageVersion);

    nb::class_<SyntaxPrinter>(m, "SyntaxPrinter")
        .def(nb::init<>())
        .def(nb::init<const SourceManager&>(), nb::keep_alive<1, 2>(), "sourceManager"_a)
        .def("append", &SyntaxPrinter::append, byrefint, "text"_a)
        .def("print", nb::overload_cast<Trivia>(&SyntaxPrinter::print), byrefint, "trivia"_a)
        .def("print", nb::overload_cast<Token>(&SyntaxPrinter::print), byrefint, "token"_a)
        .def("print", nb::overload_cast<const SyntaxNode&>(&SyntaxPrinter::print), byrefint,
             "node"_a)
        .def("print", nb::overload_cast<const SyntaxTree&>(&SyntaxPrinter::print), byrefint,
             "tree"_a)
        .def("setIncludeTrivia", &SyntaxPrinter::setIncludeTrivia, byrefint, "include"_a)
        .def("setIncludeMissing", &SyntaxPrinter::setIncludeMissing, byrefint, "include"_a)
        .def("setIncludeSkipped", &SyntaxPrinter::setIncludeSkipped, byrefint, "include"_a)
        .def("setIncludeDirectives", &SyntaxPrinter::setIncludeDirectives, byrefint, "include"_a)
        .def("setExpandMacros", &SyntaxPrinter::setExpandMacros, byrefint, "expand"_a)
        .def("setExpandIncludes", &SyntaxPrinter::setExpandIncludes, byrefint, "expand"_a)
        .def("setIncludeComments", &SyntaxPrinter::setIncludeComments, byrefint, "include"_a)
        .def("setSquashNewlines", &SyntaxPrinter::setSquashNewlines, byrefint, "include"_a)
        .def("str", &SyntaxPrinter::str)
        .def_static("printFile", &SyntaxPrinter::printFile, "tree"_a);

    nb::class_<PySyntaxRewriter>(m, "SyntaxRewriter")
        .def("remove", &PySyntaxRewriter::py_remove)
        .def("replace", &PySyntaxRewriter::py_replace, "oldNode"_a, "newNode"_a,
             "preserveTrivia"_a = false)
        .def("insertBefore", &PySyntaxRewriter::py_insertBefore)
        .def("insertAfter", &PySyntaxRewriter::py_insertAfter)
        .def("insertAtFront", &PySyntaxRewriter::py_insertAtFront<SyntaxList<SyntaxNode>>, "list"_a,
             "newNode"_a, "separator"_a = Token{})
        .def("insertAtFront", &PySyntaxRewriter::py_insertAtFront<SeparatedSyntaxList<SyntaxNode>>,
             "list"_a, "newNode"_a, "separator"_a = Token{})
        .def("insertAtBack", &PySyntaxRewriter::py_insertAtBack<SyntaxList<SyntaxNode>>, "list"_a,
             "newNode"_a, "separator"_a = Token{})
        .def("insertAtBack", &PySyntaxRewriter::py_insertAtBack<SeparatedSyntaxList<SyntaxNode>>,
             "list"_a, "newNode"_a, "separator"_a = Token{})
        .def_prop_ro("factory", &PySyntaxRewriter::getFactory,
                     "Get the SyntaxFactory for creating new syntax nodes")
        .def_prop_ro("alloc", &PySyntaxRewriter::getAllocator,
                     "Get the allocator for creating tokens and trivia")
        .def("makeToken", &PySyntaxRewriter::py_makeToken, "kind"_a, "text"_a,
             "trivia"_a = std::span<const Trivia>{},
             "Create a new token with the given kind and text")
        .def("makeToken", &PySyntaxRewriter::py_makeTokenFromKind, "kind"_a,
             "trivia"_a = std::span<const Trivia>{},
             "Create a token with text inferred from kind (for "
             "keywords/punctuation)")
        .def("makeId", &PySyntaxRewriter::py_makeId, "text"_a,
             "trivia"_a = std::span<const Trivia>{}, "Create an identifier token")
        .def("makeComma", &PySyntaxRewriter::py_makeComma, "Create a comma token")
        .def("makeTrivia", &PySyntaxRewriter::py_makeTrivia, "kind"_a, "text"_a,
             "Create a trivia with text allocated in the rewriter's allocator")
        .def("clone", &PySyntaxRewriter::py_clone, byrefint, "node"_a,
             "Create a shallow clone of the given syntax node")
        .def("deepClone", &PySyntaxRewriter::py_deepClone, byrefint, "node"_a,
             "Create a deep clone of the given syntax node and all its children")
        .def("makeList", &PySyntaxRewriter::py_makeSyntaxListGeneric, byrefint, "items"_a,
             "Create a SyntaxList from a list of syntax nodes")
        .def("makeSeparatedList", &PySyntaxRewriter::py_makeSeparatedSyntaxListGeneric, byrefint,
             "items"_a,
             "Create a SeparatedSyntaxList from a list of syntax nodes and "
             "separator tokens")
        .def("makeTokenList", &PySyntaxRewriter::py_makeTokenList, byrefint, "items"_a,
             "Create a TokenList from a list of tokens");

    m.def("rewrite", &pySyntaxRewrite, "tree"_a, "handler"_a);

    m.def(
        "clone", [](const SyntaxNode& node, BumpAllocator& alloc) { return clone(node, alloc); },
        byref, nb::keep_alive<0, 2>(), "node"_a, "alloc"_a,
        "Create a shallow clone of the given syntax node");

    m.def(
        "deepClone",
        [](const SyntaxNode& node, BumpAllocator& alloc) { return deepClone(node, alloc); }, byref,
        nb::keep_alive<0, 2>(), "node"_a, "alloc"_a,
        "Create a deep clone of the given syntax node and all its children");
}
