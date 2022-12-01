//------------------------------------------------------------------------------
// pyslang.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/parsing/Lexer.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

void registerSyntax(py::module_& m) {
    EXPOSE_ENUM(m, TriviaKind);
    EXPOSE_ENUM(m, TokenKind);
    EXPOSE_ENUM(m, SyntaxKind);

    py::class_<Trivia>(m, "Trivia")
        .def(py::init<>())
        .def(py::init<TriviaKind, string_view>(), "kind"_a, "rawText"_a)
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
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a)
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      string_view>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "strText"_a)
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      SyntaxKind>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "directive"_a)
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      logic_t>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "bit"_a)
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      const SVInt&>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "value"_a)
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      double, bool, std::optional<TimeUnit>>(),
             "alloc"_a, "kind"_a, "trivia"_a, "rawText"_a, "location"_a, "value"_a, "outOfRange"_a,
             "timeUnit"_a)
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      LiteralBase, bool>(),
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

    class SyntaxNodeIterator
        : public iterator_facade<SyntaxNodeIterator, std::forward_iterator_tag, py::object> {
    public:
        SyntaxNodeIterator(const SyntaxNode& node, size_t index) : node(&node), index(index) {
            skipToNext();
        }

        SyntaxNodeIterator& operator=(const SyntaxNodeIterator& other) {
            node = other.node;
            index = other.index;
            return *this;
        }

        py::object operator*() const {
            if (auto child = node->childNode(index))
                return py::cast(child);
            return py::cast(node->childToken(index));
        }

        bool operator==(const SyntaxNodeIterator& other) const {
            return node == other.node && index == other.index;
        }

        SyntaxNodeIterator& operator++() {
            index++;
            skipToNext();
            return *this;
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
        .def_property_readonly("sourceRange", &SyntaxNode::sourceRange)
        .def("__getitem__",
             [](const SyntaxNode& self, size_t i) -> py::object {
                 if (i >= self.getChildCount())
                     throw py::index_error();

                 if (auto node = self.childNode(i))
                     return py::cast(node);
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
        .def_readonly("isLibrary", &SyntaxTree::isLibrary)
        .def_static("fromFile", py::overload_cast<string_view>(&SyntaxTree::fromFile), "path"_a)
        .def_static("fromFile",
                    py::overload_cast<string_view, SourceManager&, const Bag&>(
                        &SyntaxTree::fromFile),
                    "path"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static("fromFiles", py::overload_cast<span<const string_view>>(&SyntaxTree::fromFiles),
                    "paths"_a)
        .def_static("fromFiles",
                    py::overload_cast<span<const string_view>, SourceManager&, const Bag&>(
                        &SyntaxTree::fromFiles),
                    "paths"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static("fromText",
                    py::overload_cast<string_view, string_view, string_view>(&SyntaxTree::fromText),
                    "text"_a, "name"_a = "source", "path"_a = "")
        .def_static(
            "fromText",
            py::overload_cast<string_view, SourceManager&, string_view, string_view, const Bag&>(
                &SyntaxTree::fromText),
            "text"_a, "sourceManager"_a, "name"_a = "source", "path"_a = "", "options"_a = Bag())
        .def_static("fromFileInMemory", &SyntaxTree::fromFileInMemory, "text"_a, "sourceManager"_a,
                    "name"_a = "source", "path"_a = "", "options"_a = Bag())
        .def_static("fromBuffer", &SyntaxTree::fromBuffer, "buffer"_a, "sourceManager"_a,
                    "options"_a = Bag(), "inheritedMacros"_a = SyntaxTree::MacroList{})
        .def_static("fromBuffers", &SyntaxTree::fromBuffers, "buffers"_a, "sourceManager"_a,
                    "options"_a = Bag(), "inheritedMacros"_a = SyntaxTree::MacroList{})
        .def_property_readonly("diagnostics", &SyntaxTree::diagnostics)
        .def_property_readonly("sourceManager", py::overload_cast<>(&SyntaxTree::sourceManager))
        .def_property_readonly("root", py::overload_cast<>(&SyntaxTree::root))
        .def_property_readonly("options", &SyntaxTree::options)
        .def_static("getDefaultSourceManager", &SyntaxTree::getDefaultSourceManager, byref);

    py::class_<LexerOptions>(m, "LexerOptions")
        .def(py::init<>())
        .def_readwrite("maxErrors", &LexerOptions::maxErrors);

    py::class_<PreprocessorOptions>(m, "PreprocessorOptions")
        .def(py::init<>())
        .def_readwrite("maxIncludeDepth", &PreprocessorOptions::maxIncludeDepth)
        .def_readwrite("predefineSource", &PreprocessorOptions::predefineSource)
        .def_readwrite("predefines", &PreprocessorOptions::predefines)
        .def_readwrite("undefines", &PreprocessorOptions::undefines);

    py::class_<ParserOptions>(m, "ParserOptions")
        .def(py::init<>())
        .def_readwrite("maxRecursionDepth", &ParserOptions::maxRecursionDepth);

    py::class_<SyntaxPrinter>(m, "SyntaxPrinter")
        .def(py::init<>())
        .def(py::init<const SourceManager&>(), "sourceManager"_a)
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
