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
#include "slang/syntax/SyntaxNode.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
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

} // end namespace

void registerSyntax(py::module_& m) {
    EXPOSE_ENUM(m, TriviaKind);
    EXPOSE_ENUM(m, TokenKind);
    EXPOSE_ENUM(m, SyntaxKind);

    py::class_<Trivia>(m, "Trivia")
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

    py::class_<Token>(m, "Token")
        .def(py::init<>())
        .def(py::init<BumpAllocator&, TokenKind, std::span<Trivia const>, std::string_view,
                      SourceLocation>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a)
        .def(py::init<BumpAllocator&, TokenKind, std::span<Trivia const>, std::string_view,
                      SourceLocation, std::string_view>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "strText"_a)
        .def(py::init<BumpAllocator&, TokenKind, std::span<Trivia const>, std::string_view,
                      SourceLocation, SyntaxKind>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "directive"_a)
        .def(py::init<BumpAllocator&, TokenKind, std::span<Trivia const>, std::string_view,
                      SourceLocation, logic_t>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "bit"_a)
        .def(py::init<BumpAllocator&, TokenKind, std::span<Trivia const>, std::string_view,
                      SourceLocation, const SVInt&>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "value"_a)
        .def(py::init<BumpAllocator&, TokenKind, std::span<Trivia const>, std::string_view,
                      SourceLocation, double, bool, std::optional<TimeUnit>>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "value"_a, "outOfRange"_a,
             "timeUnit"_a)
        .def(py::init<BumpAllocator&, TokenKind, std::span<Trivia const>, std::string_view,
                      SourceLocation, LiteralBase, bool>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "base"_a, "isSigned"_a)
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

    py::class_<SyntaxNode>(m, "SyntaxNode")
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
                 return py::cast(self.childToken(i));
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
        .def("__str__", &SyntaxNode::toString);

    py::class_<SyntaxTree, std::shared_ptr<SyntaxTree>>(m, "SyntaxTree")
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
            "path"_a, "sourceManager"_a, "options"_a = Bag())
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
            "paths"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static("fromText",
                    py::overload_cast<std::string_view, std::string_view, std::string_view>(
                        &SyntaxTree::fromText),
                    "text"_a, "name"_a = "source", "path"_a = "")
        .def_static("fromText",
                    py::overload_cast<std::string_view, SourceManager&, std::string_view,
                                      std::string_view, const Bag&, const SourceLibrary*>(
                        &SyntaxTree::fromText),
                    "text"_a, "sourceManager"_a, "name"_a = "source", "path"_a = "",
                    "options"_a = Bag(), "library"_a = nullptr)
        .def_static("fromFileInMemory", &SyntaxTree::fromFileInMemory, "text"_a, "sourceManager"_a,
                    "name"_a = "source", "path"_a = "", "options"_a = Bag())
        .def_static("fromBuffer", &SyntaxTree::fromBuffer, "buffer"_a, "sourceManager"_a,
                    "options"_a = Bag(), "inheritedMacros"_a = SyntaxTree::MacroList{})
        .def_static("fromBuffers", &SyntaxTree::fromBuffers, "buffers"_a, "sourceManager"_a,
                    "options"_a = Bag(), "inheritedMacros"_a = SyntaxTree::MacroList{})
        .def_static("fromLibraryMapFile", &SyntaxTree::fromLibraryMapFile, "path"_a,
                    "sourceManager"_a, "options"_a = Bag())
        .def_static("fromLibraryMapText", &SyntaxTree::fromLibraryMapText, "text"_a,
                    "sourceManager"_a, "name"_a = "source", "path"_a = "", "options"_a = Bag())
        .def_static("fromLibraryMapBuffer", &SyntaxTree::fromLibraryMapBuffer, "buffer"_a,
                    "sourceManager"_a, "options"_a = Bag())
        .def_property_readonly("diagnostics", &SyntaxTree::diagnostics)
        .def_property_readonly("sourceManager", py::overload_cast<>(&SyntaxTree::sourceManager))
        .def_property_readonly("root", py::overload_cast<>(&SyntaxTree::root))
        .def_property_readonly("options", &SyntaxTree::options)
        .def_property_readonly("sourceLibrary", &SyntaxTree::getSourceLibrary)
        .def_static("getDefaultSourceManager", &SyntaxTree::getDefaultSourceManager, byref);

    py::class_<LexerOptions>(m, "LexerOptions")
        .def(py::init<>())
        .def_readwrite("maxErrors", &LexerOptions::maxErrors)
        .def_readwrite("languageVersion", &LexerOptions::languageVersion);

    py::class_<PreprocessorOptions>(m, "PreprocessorOptions")
        .def(py::init<>())
        .def_readwrite("maxIncludeDepth", &PreprocessorOptions::maxIncludeDepth)
        .def_readwrite("languageVersion", &PreprocessorOptions::languageVersion)
        .def_readwrite("predefineSource", &PreprocessorOptions::predefineSource)
        .def_readwrite("predefines", &PreprocessorOptions::predefines)
        .def_readwrite("undefines", &PreprocessorOptions::undefines)
        .def_readwrite("additionalIncludePaths", &PreprocessorOptions::additionalIncludePaths)
        .def_readwrite("ignoreDirectives", &PreprocessorOptions::ignoreDirectives);

    py::class_<ParserOptions>(m, "ParserOptions")
        .def(py::init<>())
        .def_readwrite("maxRecursionDepth", &ParserOptions::maxRecursionDepth)
        .def_readwrite("languageVersion", &ParserOptions::languageVersion);

    py::class_<SyntaxPrinter>(m, "SyntaxPrinter")
        .def(py::init<>())
        .def(py::init<const SourceManager&>(), "sourceManager"_a)
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
        .def("setIncludePreprocessed", &SyntaxPrinter::setIncludePreprocessed, byrefint,
             "include"_a)
        .def("setIncludeComments", &SyntaxPrinter::setIncludeComments, byrefint, "include"_a)
        .def("setSquashNewlines", &SyntaxPrinter::setSquashNewlines, byrefint, "include"_a)
        .def("str", &SyntaxPrinter::str)
        .def_static("printFile", &SyntaxPrinter::printFile, "tree"_a);
}
