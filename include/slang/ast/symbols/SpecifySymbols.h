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

    static SpecifyBlockSymbol& fromSyntax(const Scope& scope,
                                          const syntax::SpecifyBlockSyntax& syntax,
                                          SmallVector<const Symbol*>& implicitSymbols);

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

class SLANG_EXPORT PulseStyleSymbol : public Symbol {
public:
    PulseStyleKind pulseStyleKind;

    PulseStyleSymbol(SourceLocation loc, PulseStyleKind pulseStyleKind);

    span<const Expression* const> getTerminals() const {
        if (!isResolved)
            resolve();
        return terminals;
    }

    void serializeTo(ASTSerializer& serializer) const;

    static PulseStyleSymbol& fromSyntax(const Scope& parent,
                                        const syntax::PulseStyleDeclarationSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PulseStyle; }

private:
    void resolve() const;

    mutable bool isResolved = false;
    mutable span<const Expression* const> terminals;
};

// clang-format off
#define STCK(x) \
    x(Unknown) \
    x(Setup) \
    x(Hold) \
    x(SetupHold) \
    x(Recovery) \
    x(Removal) \
    x(RecRem) \
    x(Skew) \
    x(TimeSkew) \
    x(FullSkew) \
    x(Period) \
    x(Width) \
    x(NoChange)
// clang-format on

ENUM(SystemTimingCheckKind, STCK)
#undef STCK

struct SystemTimingCheckDef;

class SLANG_EXPORT SystemTimingCheckSymbol : public Symbol {
public:
    struct EdgeDescriptor {
        char from;
        char to;
    };

    struct Arg {
        const Expression* expr = nullptr;
        const Expression* condition = nullptr;
        EdgeKind edge = EdgeKind::None;
        span<const EdgeDescriptor> edgeDescriptors;

        Arg() = default;
        Arg(const Expression& expr) : expr(&expr) {}
        Arg(const Expression& expr, const Expression* condition, EdgeKind edge,
            span<const EdgeDescriptor> edgeDescriptors) :
            expr(&expr),
            condition(condition), edge(edge), edgeDescriptors(edgeDescriptors) {}
    };

    SystemTimingCheckKind timingCheckKind;

    SystemTimingCheckSymbol(SourceLocation loc, const SystemTimingCheckDef* def);

    span<const Arg> getArguments() const {
        if (!isResolved)
            resolve();
        return args;
    }

    void serializeTo(ASTSerializer& serializer) const;

    static SystemTimingCheckSymbol& fromSyntax(const Scope& parent,
                                               const syntax::SystemTimingCheckSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::SystemTimingCheck; }

private:
    void resolve() const;

    mutable bool isResolved = false;
    mutable span<const Arg> args;
    const SystemTimingCheckDef* def;
};

} // namespace slang::ast
