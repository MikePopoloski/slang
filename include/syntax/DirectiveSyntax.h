#pragma once

#include "SyntaxNode.h"
#include "Token.h"

namespace slang {

struct DirectiveSyntax : public SyntaxNode {
    Token* directive;
    Token* endOfDirective;

    DirectiveSyntax(SyntaxKind kind, Token* directive, Token* endOfDirective) :
        SyntaxNode(kind), directive(directive), endOfDirective(endOfDirective) {}
};

struct IncludeDirectiveSyntax : public DirectiveSyntax {
    Token* fileName;

    IncludeDirectiveSyntax(Token* directive, Token* endOfDirective, Token* fileName) :
        DirectiveSyntax(SyntaxKind::IncludeDirective, directive, endOfDirective),
        fileName(fileName) {}
};

struct MacroArgumentDefaultSyntax : public SyntaxNode {
    Token* equals;
    ArrayRef<Token*> tokens;

    MacroArgumentDefaultSyntax(Token* equals, ArrayRef<Token*> tokens) :
        SyntaxNode(SyntaxKind::MacroArgumentDefault), equals(equals), tokens(tokens) {}
};

struct MacroFormalArgumentSyntax : public SyntaxNode {
    Token* name;
    MacroArgumentDefaultSyntax* defaultValue;

    MacroFormalArgumentSyntax(Token* name, MacroArgumentDefaultSyntax* def) :
        SyntaxNode(SyntaxKind::MacroFormalArgument), name(name), defaultValue(def) {}
};

struct MacroFormalArgumentListSyntax : public SyntaxNode {
    Token* openParen;
    ArrayRef<MacroFormalArgumentSyntax*> args;
    ArrayRef<Token*> commaSeparators;
    Token* closeParen;

    MacroFormalArgumentListSyntax(Token* openParen, ArrayRef<MacroFormalArgumentSyntax*> args, ArrayRef<Token*> commaSeparators, Token* closeParen) :
        SyntaxNode(SyntaxKind::MacroFormalArgumentList),
        openParen(openParen),
        args(args),
        commaSeparators(commaSeparators),
        closeParen(closeParen) {}
};

struct DefineDirectiveSyntax : public DirectiveSyntax {
    Token* name;
    MacroFormalArgumentListSyntax* formalArguments;
    ArrayRef<Token*> body;

    DefineDirectiveSyntax(Token* directive, Token* endOfDirective, Token* name, MacroFormalArgumentListSyntax* formalArguments, ArrayRef<Token*> body) :
        DirectiveSyntax(SyntaxKind::DefineDirective, directive, endOfDirective),
        name(name),
        formalArguments(formalArguments),
        body(body) {}
};

}