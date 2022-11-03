//------------------------------------------------------------------------------
//! @file SpecifySymbols.h
//! @brief Contains specify block symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Scope.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class Expression;

class SLANG_EXPORT SpecifyBlockSymbol : public Symbol, public Scope {
public:
    SpecifyBlockSymbol(Compilation& compilation, SourceLocation loc);

    static SpecifyBlockSymbol& fromSyntax(Scope& scope, const syntax::SpecifyBlockSyntax& syntax);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::SpecifyBlock; }
};

class SLANG_EXPORT TimingPathSymbol : public Symbol {
public:
    enum class ConnectionKind { Full, Parallel };
    enum class Polarity { Unknown, Positive, Negative };

    ConnectionKind connectionKind;
    Polarity polarity;
    Polarity edgePolarity;
    EdgeKind edgeIdentifier;
    bool isStateDependent = false;

    TimingPathSymbol(SourceLocation loc, ConnectionKind connectionKind, Polarity polarity,
                     Polarity edgePolarity, EdgeKind edgeIdentifier);

    const Expression* getEdgeSourceExpr() const {
        if (!isResolved)
            resolve();
        return edgeSourceExpr;
    }

    const Expression* getConditionExpr() const {
        if (!isResolved)
            resolve();
        return conditionExpr;
    }

    span<const Expression* const> getInputs() const {
        if (!isResolved)
            resolve();
        return inputs;
    }

    span<const Expression* const> getOutputs() const {
        if (!isResolved)
            resolve();
        return outputs;
    }

    span<const Expression* const> getDelays() const {
        if (!isResolved)
            resolve();
        return delays;
    }

    void serializeTo(ASTSerializer& serializer) const;

    static TimingPathSymbol& fromSyntax(const Scope& parent,
                                        const syntax::PathDeclarationSyntax& syntax);

    static TimingPathSymbol& fromSyntax(const Scope& parent,
                                        const syntax::ConditionalPathDeclarationSyntax& syntax);

    static TimingPathSymbol& fromSyntax(const Scope& parent,
                                        const syntax::IfNonePathDeclarationSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TimingPath; }

private:
    void resolve() const;

    mutable bool isResolved = false;
    mutable const Expression* edgeSourceExpr = nullptr;
    mutable const Expression* conditionExpr = nullptr;
    mutable span<const Expression* const> inputs;
    mutable span<const Expression* const> outputs;
    mutable span<const Expression* const> delays;
};

} // namespace slang::ast
