//------------------------------------------------------------------------------
//! @file BlockSymbols.h
//! @brief Contains block-related hierarchy symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/SemanticFacts.h"
#include "slang/ast/Statement.h"
#include "slang/ast/Symbol.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Function.h"

namespace slang::ast {

class Expression;
class VariableSymbol;

/// Indicates which branch of a conditional or loop generate construct
/// produced a given GenerateBlockSymbol.
#define GENERATE_BRANCH_KIND(x) \
    x(IfTrue) x(IfFalse) x(CaseItem) x(CaseDefault) x(LoopIteration) x(IllegalUnconditional)
SLANG_ENUM_SIZED(GenerateBranchKind, uint8_t, GENERATE_BRANCH_KIND)
#undef GENERATE_BRANCH_KIND

/// Represents a statement block, either sequential or parallel.
class SLANG_EXPORT StatementBlockSymbol final : public Symbol, public Scope {
public:
    StatementBlockKind blockKind;
    VariableLifetime defaultLifetime;

    StatementBlockSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                         StatementBlockKind blockKind, VariableLifetime defaultLifetime) :
        Symbol(SymbolKind::StatementBlock, name, loc), Scope(compilation, this),
        blockKind(blockKind), defaultLifetime(defaultLifetime) {}

    void setTemporaryParent(const Scope& scope, SymbolIndex index) { setParent(scope, index); }
    const Statement& getStatement(const ASTContext& context,
                                  Statement::StatementContext& stmtCtx) const;

    const Statement* tryGetStatement() const { return stmt; }

    bool isKnownBad() const { return stmt && stmt->bad(); }

    void serializeTo(ASTSerializer&) const {}

    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::BlockStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::ForLoopStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::ForeachLoopStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::ConditionalStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const syntax::PatternCaseItemSyntax& syntax);
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

    std::span<const StatementBlockSymbol* const> blocks;
    mutable const Statement* stmt = nullptr;
};

/// Represents a procedural block, such as an always block.
class SLANG_EXPORT ProceduralBlockSymbol final : public Symbol {
public:
    ProceduralBlockKind procedureKind;
    bool isFromAssertion;

    ProceduralBlockSymbol(SourceLocation loc, ProceduralBlockKind procedureKind,
                          bool isFromAssertion);

    const Statement& getBody() const;
    std::span<const StatementBlockSymbol* const> getBlocks() const { return blocks; }
    void serializeTo(ASTSerializer& serializer) const;

    bool isSingleDriverBlock() const {
        return procedureKind == ProceduralBlockKind::AlwaysComb ||
               procedureKind == ProceduralBlockKind::AlwaysLatch ||
               procedureKind == ProceduralBlockKind::AlwaysFF;
    }

    static ProceduralBlockSymbol& fromSyntax(Scope& scope,
                                             const syntax::ProceduralBlockSyntax& syntax);

    static ProceduralBlockSymbol& fromSyntax(Scope& scope,
                                             const syntax::ImmediateAssertionMemberSyntax& syntax);

    static ProceduralBlockSymbol& fromSyntax(Scope& scope,
                                             const syntax::ConcurrentAssertionMemberSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ProceduralBlock; }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return getBody().visit(visitor);
    }

private:
    std::span<const StatementBlockSymbol* const> blocks;
    const syntax::StatementSyntax* stmtSyntax = nullptr;
    mutable const Statement* stmt = nullptr;
    mutable bool isConstructing = false;

    static ProceduralBlockSymbol& createProceduralBlock(Scope& scope, ProceduralBlockKind kind,
                                                        SourceLocation location,
                                                        bool isFromAssertion,
                                                        const syntax::MemberSyntax& syntax,
                                                        const syntax::StatementSyntax& stmtSyntax);
};

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct.
class SLANG_EXPORT GenerateBlockSymbol final : public Symbol, public Scope {
public:
    uint32_t constructIndex = 0;

    /// Indicates which branch of the originating generate construct produced this block.
    GenerateBranchKind branchKind = GenerateBranchKind::IllegalUnconditional;

    bool isUninstantiated = false;
    bool isUnnamed = false;

    /// Storage for either the loop iteration index or the bound if/case condition.
    /// The active member is selected by branchKind.
    union {
        const SVInt* arrayIndex = nullptr;
        const Expression* conditionExpression;
    };

    /// Bound case-item label expressions for case-generate blocks.
    std::span<const Expression* const> caseItemExpressions = {};

    GenerateBlockSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                        uint32_t constructIndex, bool isUninstantiated) :
        Symbol(SymbolKind::GenerateBlock, name, loc), Scope(compilation, this),
        constructIndex(constructIndex), isUninstantiated(isUninstantiated),
        isUnnamed(name.empty()) {}

    /// Returns the loop-iteration index, or nullptr if this block is not a loop iteration.
    const SVInt* getArrayIndex() const {
        return branchKind == GenerateBranchKind::LoopIteration ? arrayIndex : nullptr;
    }

    /// Returns the bound if/case condition, or nullptr if this block is not a conditional branch.
    const Expression* getConditionExpression() const {
        switch (branchKind) {
            case GenerateBranchKind::IfTrue:
            case GenerateBranchKind::IfFalse:
            case GenerateBranchKind::CaseItem:
            case GenerateBranchKind::CaseDefault:
                return conditionExpression;
            default:
                return nullptr;
        }
    }

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
class SLANG_EXPORT GenerateBlockArraySymbol final : public Symbol, public Scope {
public:
    std::span<const GenerateBlockSymbol* const> entries;
    uint32_t constructIndex;
    bool valid = false;
    bool isUnnamed = false;

    /// Initial value assigned to loopVariable.
    const Expression* initialExpression = nullptr;

    /// Bound stop expression of the loop-generate.
    const Expression* stopExpression = nullptr;

    /// Bound iteration expression of the loop-generate.
    const Expression* iterExpression = nullptr;

    /// Loop variable used by the bound stop and iteration expressions.
    const VariableSymbol* loopVariable = nullptr;

    GenerateBlockArraySymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                             uint32_t constructIndex) :
        Symbol(SymbolKind::GenerateBlockArray, name, loc), Scope(compilation, this),
        constructIndex(constructIndex), isUnnamed(name.empty()) {}

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
