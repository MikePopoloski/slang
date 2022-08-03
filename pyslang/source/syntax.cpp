//------------------------------------------------------------------------------
// pyslang.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/parsing/Lexer.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

void registerSyntax(py::module_& m) {
    EXPOSE_ENUM(m, TriviaKind);
    EXPOSE_ENUM(m, TokenKind);
    EXPOSE_ENUM(m, SyntaxKind);

    py::class_<Trivia>(m, "Trivia")
        .def(py::init<>())
        .def(py::init<TriviaKind, string_view>())
        .def_readonly("kind", &Trivia::kind)
        .def("getExplicitLocation", &Trivia::getExplicitLocation)
        .def("syntax", &Trivia::syntax, py::return_value_policy::reference_internal)
        .def("getRawText", &Trivia::getRawText)
        .def("getSkippedTokens", &Trivia::getSkippedTokens)
        .def("__repr__", [](const Trivia& self) {
            return fmt::format("Trivia(TriviaKind.{})", toString(self.kind));
        });

    py::class_<Token>(m, "Token")
        .def(py::init<>())
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation>())
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      string_view>())
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      SyntaxKind>())
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      logic_t>())
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      const SVInt&>())
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      double, bool, optional<TimeUnit>>())
        .def(py::init<BumpAllocator&, TokenKind, span<Trivia const>, string_view, SourceLocation,
                      LiteralBase, bool>())
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

    py::class_<SyntaxNode>(m, "SyntaxNode")
        .def_readonly("parent", &SyntaxNode::parent)
        .def_readonly("kind", &SyntaxNode::kind)
        .def("getFirstToken", &SyntaxNode::getFirstToken)
        .def("getLastToken", &SyntaxNode::getLastToken)
        .def("childNode", &SyntaxNode::childNode)
        .def("childToken", &SyntaxNode::childToken)
        .def_property_readonly("sourceRange", &SyntaxNode::sourceRange)
        .def_property_readonly("childCount", &SyntaxNode::getChildCount)
        .def("__repr__",
             [](const SyntaxNode& self) {
                 return fmt::format("SyntaxNode(SyntaxKind.{})", toString(self.kind));
             })
        .def("__str__", &SyntaxNode::toString);

    py::class_<SyntaxTree, std::shared_ptr<SyntaxTree>>(m, "SyntaxTree")
        .def_readonly("isLibrary", &SyntaxTree::isLibrary)
        .def_static("fromFile", py::overload_cast<string_view>(&SyntaxTree::fromFile))
        .def_static(
            "fromFile",
            py::overload_cast<string_view, SourceManager&, const Bag&>(&SyntaxTree::fromFile),
            "path"_a, "sourceManager"_a, "options"_a = Bag())
        .def_static("fromText",
                    py::overload_cast<string_view, string_view, string_view>(&SyntaxTree::fromText),
                    "text"_a, "name"_a = "source", "path"_a = "")
        .def_static(
            "fromText",
            py::overload_cast<string_view, SourceManager&, string_view, string_view, const Bag&>(
                &SyntaxTree::fromText),
            "text"_a, "sourceManager"_a, "name"_a = "source", "path"_a = "", "options"_a = Bag())
        .def_property_readonly("diagnostics", &SyntaxTree::diagnostics)
        .def_property_readonly("sourceManager", py::overload_cast<>(&SyntaxTree::sourceManager))
        .def_property_readonly("root", py::overload_cast<>(&SyntaxTree::root))
        .def_property_readonly("options", &SyntaxTree::options)
        .def_static("getDefaultSourceManager", &SyntaxTree::getDefaultSourceManager);

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
}
