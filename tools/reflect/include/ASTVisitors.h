//------------------------------------------------------------------------------
//! @file ASTVisitors.h
//! @brief Reusable AST visitors
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include <iostream>
#include <ranges>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/syntax/SyntaxVisitor.h"

class PublicDirectiveVisitor : public slang::syntax::SyntaxVisitor<PublicDirectiveVisitor> {
public:
    explicit PublicDirectiveVisitor(slang::parsing::TokenKind tokenKind) : tokenKind(tokenKind) {}

    void visitToken(slang::parsing::Token token) {
        if (token.kind == tokenKind) {
            auto blockComments = token.trivia() | std::views::filter([](auto& v) {
                                     return v.kind == slang::parsing::TriviaKind::BlockComment;
                                 });

            for (auto& blockComment : blockComments) {
                isPublic = std::find(publicDirectives.begin(), publicDirectives.end(),
                                     blockComment.getRawText()) != publicDirectives.end();
            }
        }
    }

    bool operator()() { return std::exchange(isPublic, false); }

private:
    bool isPublic{false};
    slang::parsing::TokenKind tokenKind;

    constexpr static const std::array<std::string_view, 3> publicDirectives = {
        "/* public */", "/*verilator public*/", "/* verilator public */"};
};
