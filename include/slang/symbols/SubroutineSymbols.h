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

/// Specifies various flags that can apply to subroutines.
enum class MethodFlags : uint16_t {
    /// No specific flags specified.
    None = 0,

    /// The method is virtual.
    Virtual = 1 << 0,

    /// The method is 'pure' virtual, meaning it requires
    /// an implementation in derived classes.
    Pure = 1 << 1,

    /// The method is static, meaning it is invocable without
    /// an object instance handle.
    Static = 1 << 2,

    /// The method is a class constructor.
    Constructor = 1 << 3,

    /// The method is imported into an interface instance.
    InterfaceImport = 1 << 4,

    /// The method is a DPI import.
    DPIImport = 1 << 5,

    /// The method is a DPI import marked 'context'.
    DPIContext = 1 << 6,

    /// The method is known not to be constant, even if it otherwise
    /// meets all of the requirements for a constant function. Used for
    /// built-in methods only.
    NotConst = 1 << 7,

    /// This method is a std::randomize built-in. These are declared as
    /// normal subroutines so they can be found via name lookup, and then
    /// a special case translates the calls into the appropriate system
    /// subroutine call.
    Randomize = 1 << 8
};
BITMASK(MethodFlags, Randomize);

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

    ArgList getArguments() const {
        ensureElaborated();
        return arguments;
    }

    void setArguments(ArgList args) {
        arguments = args;
        cachedHasOutputArgs.reset();
    }

    /// Returns true if the subroutine has output, inout, or non-const ref arguments.
    bool hasOutputArgs() const;

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
    ArgList arguments;
    mutable const SubroutineSymbol* overrides = nullptr;
    mutable optional<bool> cachedHasOutputArgs;
};

struct ClassMethodPrototypeSyntax;
struct ModportNamedPortSyntax;
struct ModportSubroutinePortSyntax;

class MethodPrototypeSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredReturnType;
    SubroutineKind subroutineKind;
    Visibility visibility;
    bitmask<MethodFlags> flags;

    MethodPrototypeSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                          SubroutineKind subroutineKind, Visibility visibility,
                          bitmask<MethodFlags> flags);

    span<const FormalArgumentSymbol* const> getArguments() const { return arguments; }
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
    static MethodPrototypeSymbol& fromSyntax(const BindContext& context,
                                             const ModportNamedPortSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::MethodPrototype; }

private:
    span<const FormalArgumentSymbol* const> arguments;
    mutable optional<const SubroutineSymbol*> subroutine;
    mutable const Symbol* overrides = nullptr;
};

} // namespace slang
