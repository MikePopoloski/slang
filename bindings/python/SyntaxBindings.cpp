//------------------------------------------------------------------------------
// SyntaxBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "PyVisitors.h"
#include "pyslang.h"

#include "slang/parsing/Lexer.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/CSTSerializer.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/text/Json.h"
#include "slang/text/SourceManager.h"

namespace fs = std::filesystem;

namespace {

struct PySyntaxVisitor : public PyVisitorBase<PySyntaxVisitor, SyntaxVisitor> {
    using PyVisitorBase::PyVisitorBase;

    template<typename T>
    void handle(const T& t) {
        if (this->interrupted)
            return;

        // Note: the cast to SyntaxNode here is very important.
        // It means that the object Python sees is of type SyntaxNode,
        // forcing them to go through the polymorphic downcaster to get
        // at the actual type.
        py::object result = this->f(static_cast<const SyntaxNode*>(&t));
        if (result.equal(py::cast(VisitAction::Interrupt))) {
            this->interrupted = true;
            return;
        }
        if (result.not_equal(py::cast(VisitAction::Skip)))
            this->visitDefault(t);
    }

    void visitToken(parsing::Token t) {
        if (this->interrupted)
            return;
        py::object result = this->f(t);
        if (result.equal(py::cast(VisitAction::Interrupt))) {
            this->interrupted = true;
        }
    }
};

void pySyntaxVisit(const SyntaxNode& sn, py::object f) {
    PySyntaxVisitor visitor{f};
    sn.visit(visitor);
}

class PySyntaxRewriter : public SyntaxRewriter<PySyntaxRewriter> {
public:
    PySyntaxRewriter(pybind11::function handler) : handler(std::move(handler)) {}

    void visit(const SyntaxNode& node) {
        try {
            handler(pybind11::cast(&node), pybind11::cast(this));
        }
        catch (const pybind11::error_already_set& e) {
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

    void py_insertAtFront(const SyntaxListBase& list, SyntaxNode& newNode, Token separator = {}) {
        this->insertAtFront(list, cloneNode(newNode), separator);
    }

    void py_insertAtBack(const SyntaxListBase& list, SyntaxNode& newNode, Token separator = {}) {
        this->insertAtBack(list, cloneNode(newNode), separator);
    }

    SyntaxFactory& getFactory() { return factory; }

private:
    pybind11::function handler;

    SyntaxNode& cloneNode(const SyntaxNode& node) {
        return *slang::syntax::deepClone(node, this->alloc);
    }
};

std::shared_ptr<SyntaxTree> pySyntaxRewrite(const std::shared_ptr<SyntaxTree>& tree,
                                            pybind11::function handler) {
    PySyntaxRewriter rewriter(std::move(handler));
    return rewriter.transform(tree);
}

} // end namespace

void registerSyntax(py::module_& m) {
    EXPOSE_ENUM(m, TriviaKind);
    EXPOSE_ENUM(m, TokenKind);
    EXPOSE_ENUM(m, SyntaxKind);
    EXPOSE_ENUM(m, KnownSystemName);
    EXPOSE_ENUM(m, CSTJsonMode);

    py::classh<Trivia>(m, "Trivia")
        .def(py::init<>())
        .def(py::init<TriviaKind, std::string_view>(), "kind"_a, "rawText"_a)
        .def_readonly("kind", &Trivia::kind)
        .def("getExplicitLocation", &Trivia::getExplicitLocation)
        .def("syntax", &Trivia::syntax, byrefint)
        .def("getRawText", &Trivia::getRawText)
        .def("getSkippedTokens", &Trivia::getSkippedTokens)
        .def("__repr__", [](const Trivia& self) {
            return fmt::format("Trivia(TriviaKind.{})", toString(self.kind));
        });

    py::classh<Token>(m, "Token")
        .def(py::init<>())
        .def(py::init([](BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
                         std::string_view rawText, SourceLocation location) {
                 return Token(alloc, kind, alloc.copyFrom(trivia), rawText, location);
             }),
             py::keep_alive<1, 2>(), py::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
             "rawText"_a, "location"_a)
        .def(py::init([](BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
                         std::string_view rawText, SourceLocation location,
                         std::string_view strText) {
                 return Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, strText);
             }),
             py::keep_alive<1, 2>(), py::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
             "rawText"_a, "location"_a, "strText"_a)
        .def(py::init([](BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
                         std::string_view rawText, SourceLocation location, SyntaxKind directive) {
                 return Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, directive);
             }),
             py::keep_alive<1, 2>(), py::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
             "rawText"_a, "location"_a, "directive"_a)
        .def(py::init([](BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
                         std::string_view rawText, SourceLocation location, logic_t bit) {
                 return Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, bit);
             }),
             py::keep_alive<1, 2>(), py::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
             "rawText"_a, "location"_a, "bit"_a)
        .def(py::init([](BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
                         std::string_view rawText, SourceLocation location, const SVInt& value) {
                 return Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, value);
             }),
             py::keep_alive<1, 2>(), py::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
             "rawText"_a, "location"_a, "value"_a)
        .def(py::init([](BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
                         std::string_view rawText, SourceLocation location, double realValue,
                         bool outOfRange, std::optional<TimeUnit> timeUnit) {
                 return Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, realValue,
                              outOfRange, timeUnit);
             }),
             py::keep_alive<1, 2>(), py::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
             "rawText"_a, "location"_a, "value"_a, "outOfRange"_a, "timeUnit"_a)
        .def(py::init([](BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
                         std::string_view rawText, SourceLocation location, LiteralBase base,
                         bool isSigned) {
                 return Token(alloc, kind, alloc.copyFrom(trivia), rawText, location, base,
                              isSigned);
             }),
             py::keep_alive<1, 2>(), py::keep_alive<1, 4>(), "alloc"_a, "kind"_a, "trivia"_a,
             "rawText"_a, "location"_a, "base"_a, "isSigned"_a)
        .def_readonly("kind", &Token::kind)
        .def_property_readonly("isMissing", &Token::isMissing)
        .def_property_readonly("range", &Token::range)
        .def_property_readonly("location", &Token::location)
        .def_property_readonly("trivia", &Token::trivia)
        .def_property_readonly("valueText", &Token::valueText)
        .def_property_readonly("rawText", &Token::rawText)
        .def_property_readonly("isOnSameLine", &Token::isOnSameLine)
        .def_property_readonly("value",
                               [](const Token& t) -> py::object {
                                   switch (t.kind) {
                                       case TokenKind::IntegerLiteral:
                                           return py::cast(t.intValue());
                                       case TokenKind::RealLiteral:
                                       case TokenKind::TimeLiteral:
                                           return py::cast(t.realValue());
                                       case TokenKind::UnbasedUnsizedLiteral:
                                           return py::cast(t.bitValue());
                                       case TokenKind::StringLiteral:
                                       case TokenKind::Identifier:
                                           return py::cast(t.valueText());
                                       default:
                                           return py::none();
                                   }
                               })
        .def(py::self == py::self)
        .def(py::self != py::self)
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

        py::object dereference() const {
            if (auto child = node->childNode(index))
                return py::cast(child, byrefint, py::cast(node));
            return py::cast(node->childToken(index));
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

    py::classh<SyntaxNode>(m, "SyntaxNode")
        .def_readonly("parent", &SyntaxNode::parent)
        .def_readonly("kind", &SyntaxNode::kind)
        .def("getFirstToken", &SyntaxNode::getFirstToken)
        .def("getLastToken", &SyntaxNode::getLastToken)
        .def("isEquivalentTo", &SyntaxNode::isEquivalentTo, "other"_a)
        .def("visit", &pySyntaxVisit, "f"_a, PySyntaxVisitor::doc)
        .def_property_readonly("sourceRange", &SyntaxNode::sourceRange)
        .def("__getitem__",
             [](const SyntaxNode& self, size_t i) -> py::object {
                 if (i >= self.getChildCount())
                     throw py::index_error();

                 if (auto node = self.childNode(i))
                     return py::cast(node, byrefint, py::cast(&self));

                 if (auto token = self.childToken(i))
                     return py::cast(self.childToken(i));

                 return py::none();
             })
        .def("__len__", &SyntaxNode::getChildCount)
        .def(
            "__iter__",
            [](const SyntaxNode& s) {
                return py::make_iterator(SyntaxNodeIterator(s, 0),
                                         SyntaxNodeIterator(s, s.getChildCount()));
            },
            py::keep_alive<0, 1>())
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
            py::arg("mode") = CSTJsonMode::Full,
            "Convert this syntax node to JSON string with optional formatting mode");

    py::classh<IncludeMetadata>(m, "IncludeMetadata")
        .def(py::init<>())
        .def_readonly("syntax", &IncludeMetadata::syntax)
        .def_readonly("path", &IncludeMetadata::path)
        .def_readonly("buffer", &IncludeMetadata::buffer)
        .def_readonly("isSystem", &IncludeMetadata::isSystem);

    py::classh<SyntaxTree>(m, "SyntaxTree")
        .def_readonly("isLibraryUnit", &SyntaxTree::isLibraryUnit)
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
            py::keep_alive<0, 2>(), "path"_a, "sourceManager"_a, "options"_a = Bag())
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
            py::keep_alive<0, 2>(), "paths"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static("fromText",
                    py::overload_cast<std::string_view, std::string_view, std::string_view>(
                        &SyntaxTree::fromText),
                    "text"_a, "name"_a = "source", "path"_a = "")
        .def_static("fromText",
                    py::overload_cast<std::string_view, SourceManager&, std::string_view,
                                      std::string_view, const Bag&, const SourceLibrary*>(
                        &SyntaxTree::fromText),
                    py::keep_alive<0, 2>(), "text"_a, "sourceManager"_a, "name"_a = "source",
                    "path"_a = "", "options"_a = Bag(), "library"_a = nullptr)
        .def_static("fromFileInMemory", &SyntaxTree::fromFileInMemory, py::keep_alive<0, 2>(),
                    "text"_a, "sourceManager"_a, "name"_a = "source", "path"_a = "",
                    "options"_a = Bag())
        .def_static("fromBuffer", &SyntaxTree::fromBuffer, py::keep_alive<0, 2>(), "buffer"_a,
                    "sourceManager"_a, "options"_a = Bag(),
                    "inheritedMacros"_a = SyntaxTree::MacroList{})
        .def_static("fromBuffers", &SyntaxTree::fromBuffers, py::keep_alive<0, 2>(), "buffers"_a,
                    "sourceManager"_a, "options"_a = Bag(),
                    "inheritedMacros"_a = SyntaxTree::MacroList{})
        .def_static("fromLibraryMapFile", &SyntaxTree::fromLibraryMapFile, py::keep_alive<0, 2>(),
                    "path"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static("fromLibraryMapText", &SyntaxTree::fromLibraryMapText, py::keep_alive<0, 2>(),
                    "text"_a, "sourceManager"_a, "name"_a = "source", "path"_a = "",
                    "options"_a = Bag())
        .def_static("fromLibraryMapBuffer", &SyntaxTree::fromLibraryMapBuffer,
                    py::keep_alive<0, 2>(), "buffer"_a, "sourceManager"_a, "options"_a = Bag())
        .def_property_readonly("diagnostics", &SyntaxTree::diagnostics)
        .def_property_readonly("sourceManager", py::overload_cast<>(&SyntaxTree::sourceManager))
        .def_property_readonly("root", py::overload_cast<>(&SyntaxTree::root))
        .def_property_readonly("options", &SyntaxTree::options)
        .def_property_readonly("sourceLibrary", &SyntaxTree::getSourceLibrary)
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
            py::arg("mode") = CSTJsonMode::Full,
            "Convert this syntax tree to JSON string with optional formatting mode");

    py::classh<CommentHandler> commentHandler(m, "CommentHandler");
    commentHandler.def(py::init<>())
        .def(py::init<CommentHandler::Kind, std::string_view>(), "kind"_a, "endRegion"_a)
        .def_readwrite("kind", &CommentHandler::kind)
        .def_readwrite("endRegion", &CommentHandler::endRegion);

    py::native_enum<CommentHandler::Kind>(commentHandler, "Kind", "enum.Enum")
        .value("Protect", CommentHandler::Protect)
        .value("TranslateOff", CommentHandler::TranslateOff)
        .value("LintOn", CommentHandler::LintOn)
        .value("LintOff", CommentHandler::LintOff)
        .value("LintSave", CommentHandler::LintSave)
        .value("LintRestore", CommentHandler::LintRestore)
        .export_values()
        .finalize();

    py::classh<LexerOptions>(m, "LexerOptions")
        .def(py::init<>())
        .def_readwrite("maxErrors", &LexerOptions::maxErrors)
        .def_readwrite("languageVersion", &LexerOptions::languageVersion)
        .def_readwrite("enableLegacyProtect", &LexerOptions::enableLegacyProtect)
        .def_readwrite("commentHandlers", &LexerOptions::commentHandlers);

    py::classh<Lexer>(m, "Lexer")
        .def(py::init<SourceBuffer, BumpAllocator&, Diagnostics&, SourceManager&, LexerOptions>(),
             py::keep_alive<1, 3>(), py::keep_alive<1, 4>(), py::keep_alive<1, 5>(), "buffer"_a,
             "alloc"_a, "diagnostics"_a, "sourceManager"_a, "options"_a = LexerOptions())
        .def("lex", py::overload_cast<>(&Lexer::lex))
        .def("isNextTokenOnSameLine", &Lexer::isNextTokenOnSameLine)
        .def_property_readonly("library", &Lexer::getLibrary);

    py::classh<PreprocessorOptions>(m, "PreprocessorOptions")
        .def(py::init<>())
        .def_readwrite("maxIncludeDepth", &PreprocessorOptions::maxIncludeDepth)
        .def_readwrite("languageVersion", &PreprocessorOptions::languageVersion)
        .def_readwrite("predefineSource", &PreprocessorOptions::predefineSource)
        .def_readwrite("predefines", &PreprocessorOptions::predefines)
        .def_readwrite("undefines", &PreprocessorOptions::undefines)
        .def_readwrite("additionalIncludePaths", &PreprocessorOptions::additionalIncludePaths)
        .def_readwrite("ignoreDirectives", &PreprocessorOptions::ignoreDirectives);

    py::classh<ParserOptions>(m, "ParserOptions")
        .def(py::init<>())
        .def_readwrite("maxRecursionDepth", &ParserOptions::maxRecursionDepth)
        .def_readwrite("languageVersion", &ParserOptions::languageVersion);

    py::classh<SyntaxPrinter>(m, "SyntaxPrinter")
        .def(py::init<>())
        .def(py::init<const SourceManager&>(), py::keep_alive<1, 2>(), "sourceManager"_a)
        .def("append", &SyntaxPrinter::append, byrefint, "text"_a)
        .def("print", py::overload_cast<Trivia>(&SyntaxPrinter::print), byrefint, "trivia"_a)
        .def("print", py::overload_cast<Token>(&SyntaxPrinter::print), byrefint, "token"_a)
        .def("print", py::overload_cast<const SyntaxNode&>(&SyntaxPrinter::print), byrefint,
             "node"_a)
        .def("print", py::overload_cast<const SyntaxTree&>(&SyntaxPrinter::print), byrefint,
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

    py::classh<PySyntaxRewriter>(m, "SyntaxRewriter")
        .def("remove", &PySyntaxRewriter::py_remove)
        .def("replace", &PySyntaxRewriter::py_replace, "oldNode"_a, "newNode"_a,
             "preserveTrivia"_a = false)
        .def("insert_before", &PySyntaxRewriter::py_insertBefore)
        .def("insert_after", &PySyntaxRewriter::py_insertAfter)
        .def("insert_at_front", &PySyntaxRewriter::py_insertAtFront, py::arg("list"),
             py::arg("newNode"), py::arg("separator") = Token())
        .def("insert_at_back", &PySyntaxRewriter::py_insertAtBack, py::arg("list"),
             py::arg("newNode"), py::arg("separator") = Token())
        .def_property_readonly("factory", &PySyntaxRewriter::getFactory);

    m.def("rewrite", &pySyntaxRewrite, py::arg("tree"), py::arg("handler"));
}
