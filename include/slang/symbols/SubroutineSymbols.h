//------------------------------------------------------------------------------
//! @file SubroutineSymbols.h
//! @brief Contains subroutine symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Statements.h"
#include "slang/symbols/ValueSymbol.h"
#include "slang/util/Enum.h"

namespace slang {

class FormalArgumentSymbol;

enum class MethodFlags : uint8_t {
    None = 0,
    Virtual = 1,
    Pure = 2,
    Static = 4,
    Constructor = 8,
    InterfaceImport = 16,
    DPIImport = 32
};
BITMASK(MethodFlags, DPIImport);

class MethodPrototypeSymbol;
struct ClassMethodDeclarationSyntax;
struct DPIImportSyntax;
struct FunctionDeclarationSyntax;
struct FunctionPortListSyntax;

/// Represents a subroutine (task or function).
class SubroutineSymbol : public Symbol, public Scope {
public:
    using ArgList = span<const FormalArgumentSymbol* const>;

    DeclaredType declaredReturnType;
    ArgList arguments;
    VariableLifetime defaultLifetime;
    SubroutineKind subroutineKind;
    Visibility visibility = Visibility::Public;
    bitmask<MethodFlags> flags = MethodFlags::None;
    SymbolIndex outOfBlockIndex{ 0 };

    const VariableSymbol* returnValVar = nullptr;
    const VariableSymbol* thisVar = nullptr;

    SubroutineSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     VariableLifetime defaultLifetime, SubroutineKind subroutineKind) :
        Symbol(SymbolKind::Subroutine, name, loc),
        Scope(compilation, this), declaredReturnType(*this), defaultLifetime(defaultLifetime),
        subroutineKind(subroutineKind) {}

    const Statement& getBody(EvalContext* evalContext = nullptr) const;
    const Type& getReturnType() const { return declaredReturnType.getType(); }

    void setOverride(const SubroutineSymbol& parentMethod) const;
    const SubroutineSymbol* getOverride() const { return overrides; }

    bool isVirtual() const { return flags.has(MethodFlags::Virtual) || overrides != nullptr; }

    void serializeTo(ASTSerializer& serializer) const;

    static SubroutineSymbol* fromSyntax(Compilation& compilation,
                                        const FunctionDeclarationSyntax& syntax,
                                        const Scope& parent, bool outOfBlock);

    static SubroutineSymbol* fromSyntax(Compilation& compilation,
                                        const ClassMethodDeclarationSyntax& syntax,
                                        const Scope& parent);

    static SubroutineSymbol& fromSyntax(Compilation& compilation, const DPIImportSyntax& syntax,
                                        const Scope& parent);

    static SubroutineSymbol& createOutOfBlock(Compilation& compilation,
                                              const FunctionDeclarationSyntax& syntax,
                                              const MethodPrototypeSymbol& prototype,
                                              const Scope& newParent, const Scope& definitionScope,
                                              SymbolIndex outOfBlockIndex);

    static SubroutineSymbol& createFromPrototype(Compilation& compilation,
                                                 const MethodPrototypeSymbol& prototype,
                                                 const Scope& parent);

    static void buildArguments(Scope& scope, const FunctionPortListSyntax& syntax,
                               VariableLifetime defaultLifetime,
                               SmallVector<const FormalArgumentSymbol*>& arguments);

    static void checkVirtualMethodMatch(const Scope& scope, const SubroutineSymbol& parentMethod,
                                        const SubroutineSymbol& derivedMethod,
                                        bool allowDerivedReturn);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Subroutine; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        getBody().visit(visitor);
    }

private:
    void addThisVar(const Type& type);

    StatementBinder binder;
    mutable const SubroutineSymbol* overrides = nullptr;
};

struct ClassMethodPrototypeSyntax;
struct ModportNamedPortSyntax;
struct ModportSubroutinePortSyntax;

class MethodPrototypeSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredReturnType;
    span<const FormalArgumentSymbol* const> arguments;
    SubroutineKind subroutineKind;
    Visibility visibility;
    bitmask<MethodFlags> flags;

    MethodPrototypeSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                          SubroutineKind subroutineKind, Visibility visibility,
                          bitmask<MethodFlags> flags);

    const Type& getReturnType() const { return declaredReturnType.getType(); }
    const SubroutineSymbol* getSubroutine() const;

    void setOverride(const Symbol& overrideTarget) const { overrides = &overrideTarget; }
    const Symbol* getOverride() const { return overrides; }

    bool isVirtual() const { return flags.has(MethodFlags::Virtual) || overrides != nullptr; }

    bool checkMethodMatch(const Scope& scope, const SubroutineSymbol& method) const;

    void serializeTo(ASTSerializer& serializer) const;

    static MethodPrototypeSymbol& fromSyntax(const Scope& scope,
                                             const ClassMethodPrototypeSyntax& syntax);
    static MethodPrototypeSymbol& fromSyntax(const Scope& scope,
                                             const ModportSubroutinePortSyntax& syntax);
    static MethodPrototypeSymbol& fromSyntax(const Scope& scope, LookupLocation lookupLocation,
                                             const ModportNamedPortSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::MethodPrototype; }

private:
    mutable optional<const SubroutineSymbol*> subroutine;
    mutable const Symbol* overrides = nullptr;
};

} // namespace slang
