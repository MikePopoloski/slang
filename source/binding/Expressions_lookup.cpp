//------------------------------------------------------------------------------
// Expressions_lookup.cpp
// Name lookup.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Expressions.h"

#include "compilation/Compilation.h"

namespace {

using namespace slang;

// A downward lookup starts from a given scope and tries to match pieces of a name with subsequent members
// of scopes. If the entire path matches, the found member will be returned. Otherwise, the last name piece
// we looked up will be returned, along with whatever symbol was last found.
struct DownwardLookupResult {
    const Symbol* found;
    const NameSyntax* last;
};

DownwardLookupResult lookupDownward(span<const NameSyntax* const> nameParts, const Scope& scope) {
    const NameSyntax* const final = nameParts[nameParts.size() - 1];
    const Scope* current = &scope;
    const Symbol* found = nullptr;
    
    for (auto part : nameParts) {
        const Symbol* symbol;
        switch (part->kind) {
            case SyntaxKind::IdentifierName:
                symbol = current->find(part->as<IdentifierNameSyntax>().identifier.valueText());
                break;
            default:
                THROW_UNREACHABLE;
        }
    
        if (!symbol)
            return { found, part };
    
        found = symbol;
        if (part != final) {
            // This needs to be a scope, otherwise we can't do a lookup within it.
            if (!found->isScope())
                return { found, part };
            current = &found->as<Scope>();
        }
    }
    
    return { found, nullptr };
}

}

namespace slang {

Expression& Expression::bindSimpleName(Compilation& compilation, const ExpressionSyntax& syntax, const BindContext& context) {
    Token nameToken;
    const SyntaxList<ElementSelectSyntax>* selectors = nullptr;
    switch (syntax.kind) {
        case SyntaxKind::IdentifierName:
            nameToken = syntax.as<IdentifierNameSyntax>().identifier;
            break;
        case SyntaxKind::IdentifierSelectName: {
            const auto& selectSyntax = syntax.as<IdentifierSelectNameSyntax>();
            nameToken = selectSyntax.identifier;
            selectors = &selectSyntax.selectors;
            break;
        }
        default:
            THROW_UNREACHABLE;
    }

    // If the parser added a missing identifier token, it already issued an appropriate error.
    if (nameToken.valueText().empty())
        return compilation.badExpression(nullptr);

    LookupResult result;
    context.scope.lookupUnqualified(nameToken.valueText(), context.lookupLocation, context.lookupKind,
                                    nameToken.range(), result);

    if (result.hasError()) {
        compilation.addDiagnostics(result.diagnostics);
        return compilation.badExpression(nullptr);
    }

    const Symbol* symbol = result.found;
    if (!symbol) {
        // Attempt to give a more helpful error if the variable exists in scope but is declared after the lookup location.
        symbol = context.scope.find(nameToken.valueText());
        if (symbol) {
            compilation.addError(DiagCode::UsedBeforeDeclared, nameToken.range()) << nameToken.valueText();
            compilation.addError(DiagCode::NoteDeclarationHere, symbol->location);
        }
        else {
            compilation.addError(DiagCode::UndeclaredIdentifier, nameToken.range()) << nameToken.valueText();
        }
        return compilation.badExpression(nullptr);
    }

    Expression* expr = &bindSymbol(compilation, *symbol, syntax);
    if (selectors) {
        for (auto selector : *selectors)
            expr = &bindSelector(compilation, *expr, *selector, context);
    }

    return *expr;
}

Expression& Expression::bindQualifiedName(Compilation& compilation, const ScopedNameSyntax& syntax, const BindContext& context) {
    // Split the name into easier to manage chunks. The parser will always produce a left-recursive
    // name tree, so that's all we'll bother to handle.
    int colonParts = 0;
    SmallVectorSized<const NameSyntax*, 8> nameParts;
    const ScopedNameSyntax* scoped = &syntax;

    while (true) {
        nameParts.append(&scoped->right);
        if (scoped->separator.kind == TokenKind::Dot)
            colonParts = 0;
        else
            colonParts++;

        if (scoped->left.kind == SyntaxKind::ScopedName)
            scoped = &scoped->left.as<ScopedNameSyntax>();
        else
            break;
    }

    const NameSyntax* first = &scoped->left;

    // If we are starting with a colon separator, always do a downwards name resolution. If the prefix name can
    // be resolved normally, we have a class scope, otherwise it's a package lookup. See [23.7.1]
    if (colonParts) {
        Token nameToken;
        switch (first->kind) {
            case SyntaxKind::IdentifierName:
                nameToken = first->as<IdentifierNameSyntax>().identifier;
                break;
            case SyntaxKind::IdentifierSelectName:
                //nameToken = first->as<IdentifierSelectNameSyntax>().identifier;
                //break;
            default:
                THROW_UNREACHABLE;
        }

        // Try to find the prefix as a class using unqualified name lookup rules.
        LookupResult result;
        context.scope.lookupUnqualified(nameToken.valueText(), context.lookupLocation, context.lookupKind,
                                        nameToken.range(), result);

        if (result.hasError()) {
            compilation.addDiagnostics(result.diagnostics);
            return compilation.badExpression(nullptr);
        }
        
        if (result.found) {
            // TODO: handle classes
            THROW_UNREACHABLE;
        }
        
        // Otherwise, it should be a package name.
        const PackageSymbol* package = compilation.getPackage(nameToken.valueText());
        if (!package) {
            compilation.addError(DiagCode::UnknownClassOrPackage, nameToken.range()) << nameToken.valueText();
            return compilation.badExpression(nullptr);
        }

        auto downward = lookupDownward(nameParts, *package);
        if (downward.found)
            return bindSymbol(compilation, *downward.found, syntax);
    }

    return compilation.badExpression(nullptr);
}

Expression& Expression::bindSymbol(Compilation& compilation, const Symbol& symbol, const ExpressionSyntax& syntax) {
    switch (symbol.kind) {
        case SymbolKind::Variable:
        case SymbolKind::FormalArgument:
            return *compilation.emplace<VariableRefExpression>(symbol.as<VariableSymbol>(), syntax.sourceRange());

        case SymbolKind::Parameter:
            return *compilation.emplace<ParameterRefExpression>(symbol.as<ParameterSymbol>(), syntax.sourceRange());

        default:
            THROW_UNREACHABLE;
    }
}

}