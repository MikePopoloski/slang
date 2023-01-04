//------------------------------------------------------------------------------
//! @file MemberSymbols.h
//! @brief Contains member-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/ast/Scope.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class AssertionExpr;
class FormalArgumentSymbol;
class PackageSymbol;
class StatementBlockSymbol;
class TimingControl;

/// Represents an empty member, i.e. a standalone semicolon.
/// This exists as a symbol mostly to provide a place to attach attributes.
class SLANG_EXPORT EmptyMemberSymbol : public Symbol {
public:
    explicit EmptyMemberSymbol(SourceLocation location) :
        Symbol(SymbolKind::EmptyMember, "", location) {}

    void serializeTo(ASTSerializer&) const {}

    static EmptyMemberSymbol& fromSyntax(Compilation& compilation, const Scope& scope,
                                         const syntax::EmptyMemberSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EmptyMember; }
};

/// A class that wraps a hoisted transparent type member, such as an enum value
/// or a symbol inherited from a base class, into a scope. Whenever lookup finds
/// one of these symbols, it will be unwrapped into the underlying symbol instead.
class SLANG_EXPORT TransparentMemberSymbol : public Symbol {
public:
    const Symbol& wrapped;

    TransparentMemberSymbol(const Symbol& wrapped_) :
        Symbol(SymbolKind::TransparentMember, wrapped_.name, wrapped_.location), wrapped(wrapped_) {
    }

    // Wrapped symbols will be exposed in their containing scope.
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TransparentMember; }
};

/// Represents an explicit import from a package.
class SLANG_EXPORT ExplicitImportSymbol : public Symbol {
public:
    string_view packageName;
    string_view importName;
    bool isFromExport = false;

    ExplicitImportSymbol(string_view packageName, string_view importName, SourceLocation location) :
        Symbol(SymbolKind::ExplicitImport, importName, location), packageName(packageName),
        importName(importName) {}

    const PackageSymbol* package() const;
    const Symbol* importedSymbol() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ExplicitImport; }

private:
    mutable const PackageSymbol* package_ = nullptr;
    mutable const Symbol* import = nullptr;
    mutable bool initialized = false;
};

/// Represents a wildcard import declaration. This symbol is special in
/// that it won't be returned by a lookup, and won't even be in the name
/// map of a symbol at all. Instead there is a sideband list used to
/// resolve names via wildcard.
class SLANG_EXPORT WildcardImportSymbol : public Symbol {
public:
    string_view packageName;
    bool isFromExport = false;

    WildcardImportSymbol(string_view packageName, SourceLocation location) :
        Symbol(SymbolKind::WildcardImport, "", location), packageName(packageName) {}

    void setPackage(const PackageSymbol& package);
    const PackageSymbol* getPackage() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::WildcardImport; }

private:
    mutable std::optional<const PackageSymbol*> package;
};

/// Represents a single port specifier in a modport declaration.
class SLANG_EXPORT ModportPortSymbol : public ValueSymbol {
public:
    /// The direction of data flowing across the port.
    ArgumentDirection direction = ArgumentDirection::InOut;

    /// An instance-internal symbol that this port connects to, if any.
    /// Ports that do not connect directly to an internal symbol will have
    /// this set to nullptr.
    const Symbol* internalSymbol = nullptr;

    /// An optional explicit expression that defines how the port connects
    /// to members internal to the instance.
    const Expression* explicitConnection = nullptr;

    ModportPortSymbol(string_view name, SourceLocation loc, ArgumentDirection direction);

    void serializeTo(ASTSerializer& serializer) const;

    static ModportPortSymbol& fromSyntax(const ASTContext& context, ArgumentDirection direction,
                                         const syntax::ModportNamedPortSyntax& syntax);

    static ModportPortSymbol& fromSyntax(const ASTContext& context, ArgumentDirection direction,
                                         const syntax::ModportExplicitPortSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModportPort; }
};

/// Represents a clocking block port.
class SLANG_EXPORT ModportClockingSymbol : public Symbol {
public:
    /// The target clocking block of the modport.
    const Symbol* target = nullptr;

    ModportClockingSymbol(string_view name, SourceLocation loc);

    void serializeTo(ASTSerializer& serializer) const;

    static ModportClockingSymbol& fromSyntax(const ASTContext& context,
                                             const syntax::ModportClockingPortSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModportClocking; }
};

/// Represents a modport within an interface definition.
class SLANG_EXPORT ModportSymbol : public Symbol, public Scope {
public:
    bool hasExports = false;

    ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    void serializeTo(ASTSerializer&) const {}

    static void fromSyntax(const ASTContext& context,
                           const syntax::ModportDeclarationSyntax& syntax,
                           SmallVectorBase<const ModportSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Modport; }
};

/// Represents a continuous assignment statement.
class SLANG_EXPORT ContinuousAssignSymbol : public Symbol {
public:
    explicit ContinuousAssignSymbol(const syntax::ExpressionSyntax& syntax);
    ContinuousAssignSymbol(SourceLocation loc, const Expression& assignment);

    const Expression& getAssignment() const;
    const TimingControl* getDelay() const;
    std::pair<std::optional<DriveStrength>, std::optional<DriveStrength>> getDriveStrength() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation, const syntax::ContinuousAssignSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ContinuousAssign; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return getAssignment().visit(visitor);
    }

private:
    mutable const Expression* assign = nullptr;
    mutable std::optional<const TimingControl*> delay;
};

/// Represents a genvar declaration.
class SLANG_EXPORT GenvarSymbol : public Symbol {
public:
    GenvarSymbol(string_view name, SourceLocation loc);

    void serializeTo(ASTSerializer&) const {}

    static void fromSyntax(const Scope& parent, const syntax::GenvarDeclarationSyntax& syntax,
                           SmallVectorBase<const GenvarSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Genvar; }
};

/// Represents an elaboration system task, such as $error or $warning.
class SLANG_EXPORT ElabSystemTaskSymbol : public Symbol {
public:
    ElabSystemTaskKind taskKind;

    ElabSystemTaskSymbol(ElabSystemTaskKind taskKind, SourceLocation loc);

    string_view getMessage() const;
    const Expression* getAssertCondition() const;
    void issueDiagnostic() const;

    void serializeTo(ASTSerializer& serializer) const;

    static ElabSystemTaskSymbol& fromSyntax(Compilation& compilation,
                                            const syntax::ElabSystemTaskSyntax& syntax);

    static string_view createMessage(const ASTContext& context, span<const Expression* const> args);

    static void reportStaticAssert(const Scope& scope, SourceLocation loc, string_view message,
                                   const Expression* condition);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ElabSystemTask; }

private:
    mutable std::optional<string_view> message;
    mutable const Expression* assertCondition = nullptr;
};

class SLANG_EXPORT PrimitivePortSymbol : public ValueSymbol {
public:
    PrimitivePortDirection direction;

    PrimitivePortSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                        PrimitivePortDirection direction);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PrimitivePort; }
};

class SLANG_EXPORT PrimitiveSymbol : public Symbol, public Scope {
public:
    span<const PrimitivePortSymbol* const> ports;
    const ConstantValue* initVal = nullptr;
    bool isSequential = false;
    enum PrimitiveKind { UserDefined, Fixed, NInput, NOutput } primitiveKind;

    PrimitiveSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                    PrimitiveKind primitiveKind) :
        Symbol(SymbolKind::Primitive, name, loc),
        Scope(compilation, this), primitiveKind(primitiveKind) {}

    static PrimitiveSymbol& fromSyntax(const Scope& scope,
                                       const syntax::UdpDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Primitive; }
};

/// Represents a formal argument / port of an assertion construct, such
/// as a sequence, property, or let construct.
class SLANG_EXPORT AssertionPortSymbol : public Symbol {
public:
    DeclaredType declaredType;
    const syntax::PropertyExprSyntax* defaultValueSyntax = nullptr;
    std::optional<ArgumentDirection> localVarDirection;

    AssertionPortSymbol(string_view name, SourceLocation loc);

    bool isLocalVar() const { return localVarDirection.has_value(); }

    static void buildPorts(Scope& scope, const syntax::AssertionItemPortListSyntax& syntax,
                           SmallVectorBase<const AssertionPortSymbol*>& results);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::AssertionPort; }
};

/// Represents a named sequence object.
class SLANG_EXPORT SequenceSymbol : public Symbol, public Scope {
public:
    span<const AssertionPortSymbol* const> ports;

    SequenceSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    static SequenceSymbol& fromSyntax(const Scope& scope,
                                      const syntax::SequenceDeclarationSyntax& syntax);

    void makeDefaultInstance() const;

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Sequence; }
};

/// Represents a named property object.
class SLANG_EXPORT PropertySymbol : public Symbol, public Scope {
public:
    span<const AssertionPortSymbol* const> ports;

    PropertySymbol(Compilation& compilation, string_view name, SourceLocation loc);

    static PropertySymbol& fromSyntax(const Scope& scope,
                                      const syntax::PropertyDeclarationSyntax& syntax);

    void makeDefaultInstance() const;

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Property; }
};

/// Represents a let declaration.
class SLANG_EXPORT LetDeclSymbol : public Symbol, public Scope {
public:
    span<const AssertionPortSymbol* const> ports;
    not_null<const syntax::ExpressionSyntax*> exprSyntax;

    LetDeclSymbol(Compilation& compilation, const syntax::ExpressionSyntax& exprSyntax,
                  string_view name, SourceLocation loc);

    static LetDeclSymbol& fromSyntax(const Scope& scope,
                                     const syntax::LetDeclarationSyntax& syntax);

    void makeDefaultInstance() const;

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::LetDecl; }
};

/// Represents a clocking block.
class SLANG_EXPORT ClockingBlockSymbol : public Symbol, public Scope {
public:
    ClockingBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    const TimingControl& getEvent() const;
    ClockingSkew getDefaultInputSkew() const;
    ClockingSkew getDefaultOutputSkew() const;

    static ClockingBlockSymbol& fromSyntax(const Scope& scope,
                                           const syntax::ClockingDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClockingBlock; }

private:
    mutable const TimingControl* event = nullptr;
    mutable std::optional<ClockingSkew> defaultInputSkew;
    mutable std::optional<ClockingSkew> defaultOutputSkew;
    const syntax::ClockingSkewSyntax* inputSkewSyntax = nullptr;
    const syntax::ClockingSkewSyntax* outputSkewSyntax = nullptr;
};

class SLANG_EXPORT RandSeqProductionSymbol : public Symbol, public Scope {
public:
    enum class ProdKind { Item, CodeBlock, IfElse, Repeat, Case };

    struct ProdBase {
        ProdKind kind;

        explicit ProdBase(ProdKind kind) : kind(kind) {}
    };

    struct ProdItem : public ProdBase {
        const RandSeqProductionSymbol* target;
        span<const Expression* const> args;

        ProdItem(const RandSeqProductionSymbol* target, span<const Expression* const> args) :
            ProdBase(ProdKind::Item), target(target), args(args) {}

        template<typename TVisitor>
        void visitExprs(TVisitor&& visitor) const {
            for (auto arg : args)
                arg->visit(visitor);
        }
    };

    struct CodeBlockProd : public ProdBase {
        not_null<const StatementBlockSymbol*> block;

        explicit CodeBlockProd(const StatementBlockSymbol& block) :
            ProdBase(ProdKind::CodeBlock), block(&block) {}
    };

    struct IfElseProd : public ProdBase {
        not_null<const Expression*> expr;
        ProdItem ifItem;
        std::optional<ProdItem> elseItem;

        IfElseProd(const Expression& expr, ProdItem ifItem, std::optional<ProdItem> elseItem) :
            ProdBase(ProdKind::IfElse), expr(&expr), ifItem(ifItem), elseItem(elseItem) {}
    };

    struct RepeatProd : public ProdBase {
        not_null<const Expression*> expr;
        ProdItem item;

        RepeatProd(const Expression& expr, ProdItem item) :
            ProdBase(ProdKind::Repeat), expr(&expr), item(item) {}
    };

    struct CaseItem {
        span<const Expression* const> expressions;
        ProdItem item;
    };

    struct CaseProd : public ProdBase {
        not_null<const Expression*> expr;
        span<const CaseItem> items;
        std::optional<ProdItem> defaultItem;

        CaseProd(const Expression& expr, span<const CaseItem> items,
                 std::optional<ProdItem> defaultItem) :
            ProdBase(ProdKind::Case),
            expr(&expr), items(items), defaultItem(defaultItem) {}
    };

    struct Rule {
        not_null<const StatementBlockSymbol*> ruleBlock;
        span<const ProdBase* const> prods;
        const Expression* weightExpr;
        const Expression* randJoinExpr;
        std::optional<CodeBlockProd> codeBlock;
        bool isRandJoin;

        Rule(const StatementBlockSymbol& ruleBlock, span<const ProdBase* const> prods,
             const Expression* weightExpr, const Expression* randJoinExpr,
             std::optional<CodeBlockProd> codeBlock, bool isRandJoin) :
            ruleBlock(&ruleBlock),
            prods(prods), weightExpr(weightExpr), randJoinExpr(randJoinExpr), codeBlock(codeBlock),
            isRandJoin(isRandJoin) {}
    };

    DeclaredType declaredReturnType;
    span<const FormalArgumentSymbol* const> arguments;

    RandSeqProductionSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    span<const Rule> getRules() const;
    const Type& getReturnType() const { return declaredReturnType.getType(); }

    void serializeTo(ASTSerializer& serializer) const;

    static RandSeqProductionSymbol& fromSyntax(Compilation& compilation,
                                               const syntax::ProductionSyntax& syntax);

    static const RandSeqProductionSymbol* findProduction(string_view name, SourceRange nameRange,
                                                         const ASTContext& context);

    static void createRuleVariables(const syntax::RsRuleSyntax& syntax, const Scope& scope,
                                    SmallVectorBase<const Symbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::RandSeqProduction; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& rule : getRules()) {
            for (auto prod : rule.prods) {
                switch (prod->kind) {
                    case ProdKind::Item:
                        ((const ProdItem*)prod)->visitExprs(visitor);
                        break;
                    case ProdKind::CodeBlock:
                        break;
                    case ProdKind::IfElse: {
                        auto& iep = *(const IfElseProd*)prod;
                        iep.expr->visit(visitor);
                        iep.ifItem.visitExprs(visitor);
                        if (iep.elseItem)
                            iep.elseItem->visitExprs(visitor);
                        break;
                    }
                    case ProdKind::Repeat: {
                        auto& rp = *(const RepeatProd*)prod;
                        rp.expr->visit(visitor);
                        rp.item.visitExprs(visitor);
                        break;
                    }
                    case ProdKind::Case: {
                        auto& cp = *(const CaseProd*)prod;
                        cp.expr->visit(visitor);
                        if (cp.defaultItem)
                            cp.defaultItem->visitExprs(visitor);

                        for (auto& item : cp.items) {
                            for (auto expr : item.expressions)
                                expr->visit(visitor);

                            item.item.visitExprs(visitor);
                        }
                        break;
                    }
                    default:
                        ASSUME_UNREACHABLE;
                }
            }

            if (rule.weightExpr)
                rule.weightExpr->visit(visitor);

            if (rule.randJoinExpr)
                rule.randJoinExpr->visit(visitor);
        }
    }

private:
    static Rule createRule(const syntax::RsRuleSyntax& syntax, const ASTContext& context,
                           const StatementBlockSymbol& ruleBlock);
    static ProdItem createProdItem(const syntax::RsProdItemSyntax& syntax,
                                   const ASTContext& context);
    static const CaseProd& createCaseProd(const syntax::RsCaseSyntax& syntax,
                                          const ASTContext& context);

    mutable std::optional<span<const Rule>> rules;
};

class SLANG_EXPORT AnonymousProgramSymbol : public Symbol, public Scope {
public:
    AnonymousProgramSymbol(Compilation& compilation, SourceLocation loc);

    static AnonymousProgramSymbol& fromSyntax(Scope& scope,
                                              const syntax::AnonymousProgramSyntax& syntax);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::AnonymousProgram; }
};

} // namespace slang::ast
