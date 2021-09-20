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
    const Statement& getBody() const;

    void serializeTo(ASTSerializer&) const {}

    static StatementBlockSymbol& fromSyntax(const Scope& scope, const BlockStatementSyntax& syntax,
                                            bitmask<StatementFlags> flags);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const ForLoopStatementSyntax& syntax,
                                            bitmask<StatementFlags> flags);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const ForeachLoopStatementSyntax& syntax,
                                            bitmask<StatementFlags> flags);
    static StatementBlockSymbol& fromSyntax(const Scope& scope,
                                            const RandSequenceStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope, const RsRuleSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(const Scope& scope, const RsCodeBlockSyntax& syntax);
    static StatementBlockSymbol& fromLabeledStmt(const Scope& scope, const StatementSyntax& syntax,
                                                 bitmask<StatementFlags> flags);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::StatementBlock; }

private:
    friend Scope;

    void elaborateVariables(function_ref<void(const Symbol&)> insertCB) const;

    StatementBinder binder;
};

struct ConcurrentAssertionMemberSyntax;
struct ImmediateAssertionMemberSyntax;
struct MemberSyntax;
struct ProceduralBlockSyntax;
struct StatementSyntax;

class ProceduralBlockSymbol : public Symbol {
public:
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(SourceLocation loc, ProceduralBlockKind procedureKind) :
        Symbol(SymbolKind::ProceduralBlock, "", loc), procedureKind(procedureKind) {}

    const Statement& getBody() const;
    void serializeTo(ASTSerializer& serializer) const;

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
    StatementBinder binder;

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
    struct ArrayEntry {
        not_null<const SVInt*> index;
        not_null<const GenerateBlockSymbol*> block;
    };

    span<const ArrayEntry> entries;
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
