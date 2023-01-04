//------------------------------------------------------------------------------
//! @file BlockSymbols.h
//! @brief Contains block-related hierarchy symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/SemanticFacts.h"
#include "slang/ast/Statements.h"
#include "slang/ast/Symbol.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Function.h"

namespace slang::ast {

class SLANG_EXPORT StatementBlockSymbol : public Symbol, public Scope {
public:
    StatementBlockKind blockKind;
    VariableLifetime defaultLifetime;

    StatementBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                         StatementBlockKind blockKind, VariableLifetime defaultLifetime) :
        Symbol(SymbolKind::StatementBlock, name, loc),
        Scope(compilation, this), blockKind(blockKind), defaultLifetime(defaultLifetime) {}

    void setTemporaryParent(const Scope& scope, SymbolIndex index) { setParent(scope, index); }
    const Statement& getStatement(const ASTContext& context,
                                  Statement::StatementContext& stmtCtx) const;

    void serializeTo(ASTSerializer&) const {}

    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::BlockStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::ForLoopStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::ForeachLoopStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::RandSequenceStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope, const syntax::RsRuleSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::RsCodeBlockSyntax& syntax);
    static StatementBlockSymbol& fromLabeledStmt(const Scope& scope,
                                                 const syntax::StatementSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::StatementBlock; }

private:
    friend Scope;

    void elaborateVariables(function_ref<void(const Symbol&)> insertCB) const;

    span<const StatementBlockSymbol* const> blocks;
    mutable const Statement* stmt = nullptr;
};

class SLANG_EXPORT ProceduralBlockSymbol : public Symbol {
public:
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(SourceLocation loc, ProceduralBlockKind procedureKind);

    const Statement& getBody() const;
    void serializeTo(ASTSerializer& serializer) const;

    bool isSingleDriverBlock() const {
        return procedureKind == ProceduralBlockKind::AlwaysComb ||
               procedureKind == ProceduralBlockKind::AlwaysLatch ||
               procedureKind == ProceduralBlockKind::AlwaysFF;
    }

    static ProceduralBlockSymbol& fromSyntax(
        const Scope& scope, const syntax::ProceduralBlockSyntax& syntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);

    static ProceduralBlockSymbol& fromSyntax(
        const Scope& scope, const syntax::ImmediateAssertionMemberSyntax& syntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);

    static ProceduralBlockSymbol& fromSyntax(
        const Scope& scope, const syntax::ConcurrentAssertionMemberSyntax& syntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ProceduralBlock; }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return getBody().visit(visitor);
    }

private:
    span<const StatementBlockSymbol* const> blocks;
    const syntax::StatementSyntax* stmtSyntax = nullptr;
    mutable const Statement* stmt = nullptr;
    mutable bool isConstructing = false;

    static ProceduralBlockSymbol& createProceduralBlock(
        const Scope& scope, ProceduralBlockKind kind, SourceLocation location,
        const syntax::MemberSyntax& syntax, const syntax::StatementSyntax& stmtSyntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);
};

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct.
class SLANG_EXPORT GenerateBlockSymbol : public Symbol, public Scope {
public:
    uint32_t constructIndex = 0;
    bool isUninstantiated = false;
    const SVInt* arrayIndex = nullptr;

    GenerateBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                        uint32_t constructIndex, bool isUninstantiated) :
        Symbol(SymbolKind::GenerateBlock, name, loc),
        Scope(compilation, this), constructIndex(constructIndex),
        isUninstantiated(isUninstantiated) {}

    std::string getExternalName() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation, const syntax::IfGenerateSyntax& syntax,
                           const ASTContext& context, uint32_t constructIndex,
                           bool isUninstantiated, SmallVectorBase<GenerateBlockSymbol*>& results);

    static void fromSyntax(Compilation& compilation, const syntax::CaseGenerateSyntax& syntax,
                           const ASTContext& context, uint32_t constructIndex,
                           bool isUninstantiated, SmallVectorBase<GenerateBlockSymbol*>& results);

    static GenerateBlockSymbol& fromSyntax(const Scope& scope,
                                           const syntax::GenerateBlockSyntax& syntax,
                                           uint32_t constructIndex);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenerateBlock; }
};

/// Represents an array of generate blocks, as generated by a loop generate construct.
class SLANG_EXPORT GenerateBlockArraySymbol : public Symbol, public Scope {
public:
    span<const GenerateBlockSymbol* const> entries;
    uint32_t constructIndex;
    bool valid = false;

    GenerateBlockArraySymbol(Compilation& compilation, string_view name, SourceLocation loc,
                             uint32_t constructIndex) :
        Symbol(SymbolKind::GenerateBlockArray, name, loc),
        Scope(compilation, this), constructIndex(constructIndex) {}

    std::string getExternalName() const;

    void serializeTo(ASTSerializer& serializer) const;

    /// Creates a generate block array from the given loop-generate syntax node.
    static GenerateBlockArraySymbol& fromSyntax(Compilation& compilation,
                                                const syntax::LoopGenerateSyntax& syntax,
                                                SymbolIndex scopeIndex, const ASTContext& context,
                                                uint32_t constructIndex);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenerateBlockArray; }
};

} // namespace slang::ast
