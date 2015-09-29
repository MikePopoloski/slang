#pragma once

#include "SyntaxNode.h"
#include "Token.h"

namespace slang {

struct DirectiveSyntax : public SyntaxNode {
    Token* directive;
    Token* endOfDirective;

    DirectiveSyntax(SyntaxKind kind, Token* directive, Token* endOfDirective) :
        SyntaxNode(kind), directive(directive), endOfDirective(endOfDirective)
    {
        childCount += 2;
    }

protected:
    TokenOrSyntax getChild(uint32_t index) const override;
};

struct IncludeDirectiveSyntax : public DirectiveSyntax {
    Token* fileName;

    IncludeDirectiveSyntax(Token* directive, Token* endOfDirective, Token* fileName) :
        DirectiveSyntax(SyntaxKind::IncludeDirective, directive, endOfDirective),
        fileName(fileName)
    {
        childCount += 1;
    }

protected:
    TokenOrSyntax getChild(uint32_t index) const override final;
};

struct MacroArgumentDefaultSyntax : public SyntaxNode {
    Token* equals;
    TokenList tokens;

    MacroArgumentDefaultSyntax(Token* equals, TokenList tokens) :
        SyntaxNode(SyntaxKind::MacroArgumentDefault), equals(equals), tokens(tokens)
    {
        childCount += 2;
    }

protected:
    TokenOrSyntax getChild(uint32_t index) const override final;
};

struct MacroFormalArgumentSyntax : public SyntaxNode {
    Token* name;
    MacroArgumentDefaultSyntax* defaultValue;

    MacroFormalArgumentSyntax(Token* name, MacroArgumentDefaultSyntax* def) :
        SyntaxNode(SyntaxKind::MacroFormalArgument), name(name), defaultValue(def)
    {
        childCount += 2;
    }

protected:
    TokenOrSyntax getChild(uint32_t index) const override final;
};

struct MacroFormalArgumentListSyntax : public SyntaxNode {
    Token* openParen;
    SeparatedSyntaxList<MacroFormalArgumentSyntax> args;
    Token* closeParen;

    MacroFormalArgumentListSyntax(Token* openParen, SeparatedSyntaxList<MacroFormalArgumentSyntax> args, Token* closeParen) :
        SyntaxNode(SyntaxKind::MacroFormalArgumentList),
        openParen(openParen),
        args(args),
        closeParen(closeParen)
    {
        childCount += 3;
    }

protected:
    TokenOrSyntax getChild(uint32_t index) const override final;
};

struct DefineDirectiveSyntax : public DirectiveSyntax {
    Token* name;
    MacroFormalArgumentListSyntax* formalArguments;
    TokenList body;

    DefineDirectiveSyntax(Token* directive, Token* endOfDirective, Token* name, MacroFormalArgumentListSyntax* formalArguments, TokenList body) :
        DirectiveSyntax(SyntaxKind::DefineDirective, directive, endOfDirective),
        name(name),
        formalArguments(formalArguments),
        body(body)
    {
        childCount += 3;
    }

protected:
    TokenOrSyntax getChild(uint32_t index) const override final;
};

}