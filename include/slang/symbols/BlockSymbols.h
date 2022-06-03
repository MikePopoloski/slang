//------------------------------------------------------------------------------
//! @file BlockSymbols.h
//! @brief Contains block-related hierarchy symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Statements.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"
#include "slang/util/Function.h"

namespace slang {

struct RsCodeBlockSyntax;
struct RsRuleSyntax;

class StatementBlockSymbol : public Symbol, public Scope {
public:
    StatementBlockKind blockKind;
    VariableLifetime defaultLifetime;

    StatementBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                         StatementBlockKind blockKind, VariableLifetime defaultLifetime) :
        Symbol(SymbolKind::StatementBlock, name, loc),
        Scope(compilation, this), blockKind(blockKind), defaultLifetime(defaultLifetime) {}

    void setTemporaryParent(const Scope& scope, SymbolIndex index) { setParent(scope, index); }
    const Statement& getStatement(const BindContext& context,
                                  Statement::StatementContext& stmtCtx) const;

    void serializeTo(ASTSerializer&) const {}

    static StatementBlockSymbol& fromSyntax(const Scope& scope, const BlockStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const ForLoopStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const ForeachLoopStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const RandSequenceStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope, const RsRuleSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope, const RsCodeBlockSyntax& syntax);
    static StatementBlockSymbol& fromLabeledStmt(const Scope& scope, const StatementSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::StatementBlock; }

private:
    friend Scope;

    void elaborateVariables(function_ref<void(const Symbol&)> insertCB) const;

    span<const StatementBlockSymbol* const> blocks;
    mutable const Statement* stmt = nullptr;
};

struct ConcurrentAssertionMemberSyntax;
struct ImmediateAssertionMemberSyntax;
struct MemberSyntax;
struct ProceduralBlockSyntax;
struct StatementSyntax;

class ProceduralBlockSymbol : public Symbol {
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
        const Scope& scope, const ProceduralBlockSyntax& syntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);

    static ProceduralBlockSymbol& fromSyntax(
        const Scope& scope, const ImmediateAssertionMemberSyntax& syntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);

    static ProceduralBlockSymbol& fromSyntax(
        const Scope& scope, const ConcurrentAssertionMemberSyntax& syntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ProceduralBlock; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        getBody().visit(visitor);
    }

private:
    span<const StatementBlockSymbol* const> blocks;
    const StatementSyntax* stmtSyntax = nullptr;
    mutable const Statement* stmt = nullptr;
    mutable bool isBinding = false;

    static ProceduralBlockSymbol& createProceduralBlock(
        const Scope& scope, ProceduralBlockKind kind, SourceLocation location,
        const MemberSyntax& syntax, const StatementSyntax& stmtSyntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);
};

struct CaseGenerateSyntax;
struct IfGenerateSyntax;
struct GenerateBlockSyntax;

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct.
class GenerateBlockSymbol : public Symbol, public Scope {
public:
    uint32_t constructIndex = 0;
    bool isInstantiated = false;
    const SVInt* arrayIndex = nullptr;

    GenerateBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                        uint32_t constructIndex, bool isInstantiated) :
        Symbol(SymbolKind::GenerateBlock, name, loc),
        Scope(compilation, this), constructIndex(constructIndex), isInstantiated(isInstantiated) {}

    std::string getExternalName() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                           const BindContext& context, uint32_t constructIndex, bool isInstantiated,
                           SmallVector<GenerateBlockSymbol*>& results);

    static void fromSyntax(Compilation& compilation, const CaseGenerateSyntax& syntax,
                           const BindContext& context, uint32_t constructIndex, bool isInstantiated,
                           SmallVector<GenerateBlockSymbol*>& results);

    static GenerateBlockSymbol& fromSyntax(const Scope& scope, const GenerateBlockSyntax& syntax,
                                           uint32_t constructIndex);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenerateBlock; }
};

struct LoopGenerateSyntax;

/// Represents an array of generate blocks, as generated by a loop generate construct.
class GenerateBlockArraySymbol : public Symbol, public Scope {
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
                                                const LoopGenerateSyntax& syntax,
                                                SymbolIndex scopeIndex, const BindContext& context,
                                                uint32_t constructIndex);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenerateBlockArray; }
};

} // namespace slang
