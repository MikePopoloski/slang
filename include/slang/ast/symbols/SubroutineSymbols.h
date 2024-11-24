//------------------------------------------------------------------------------
//! @file SubroutineSymbols.h
//! @brief Contains subroutine symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Scope.h"
#include "slang/ast/types/DeclaredType.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Enum.h"

namespace slang::ast {

class FormalArgumentSymbol;
class Statement;
class StatementBlockSymbol;
class VariableSymbol;

/// Specifies various flags that can apply to subroutines.
enum class SLANG_EXPORT MethodFlags : uint16_t {
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

    /// The method is declared extern from an interface,
    /// and so its body must be exported by a module elsewhere.
    InterfaceExtern = 1 << 4,

    /// The method is imported via a modport.
    ModportImport = 1 << 5,

    /// The method is exported via a modport.
    ModportExport = 1 << 6,

    /// The method is a DPI import.
    DPIImport = 1 << 7,

    /// The method is a DPI import marked 'context'.
    DPIContext = 1 << 8,

    /// The method is built-in via language rules,
    /// as opposed to defined by the user.
    BuiltIn = 1 << 9,

    /// This method is a std::randomize built-in. These are declared as
    /// normal subroutines so they can be found via name lookup, and then
    /// a special case translates the calls into the appropriate system
    /// subroutine call.
    Randomize = 1 << 10,

    /// Used with InterfaceExtern methods to indicate that more than one
    /// module is allowed to export the same task.
    ForkJoin = 1 << 11,

    /// The method is a constructor that has a 'default' argument
    /// indicating that the parent class's argument list should be inserted.
    DefaultedSuperArg = 1 << 12,

    /// The method is marked 'initial', which means it should not
    /// override a base class method.
    Initial = 1 << 13,

    /// The method is marked 'extends', which means it must override
    /// a base class method (and also it will be virtual).
    Extends = 1 << 14,

    /// The method is marked 'final', which means it cannot be
    /// overridden in a derived class.
    Final = 1 << 15
};
SLANG_BITMASK(MethodFlags, Final)

class MethodPrototypeSymbol;

/// Represents a subroutine (task or function).
class SLANG_EXPORT SubroutineSymbol : public Symbol, public Scope {
public:
    using ArgList = std::span<const FormalArgumentSymbol* const>;

    DeclaredType declaredReturnType;
    VariableLifetime defaultLifetime;
    SubroutineKind subroutineKind;
    Visibility visibility = Visibility::Public;
    bitmask<MethodFlags> flags = MethodFlags::None;
    SymbolIndex outOfBlockIndex{0};

    const VariableSymbol* returnValVar = nullptr;
    const VariableSymbol* thisVar = nullptr;

    SubroutineSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                     VariableLifetime defaultLifetime, SubroutineKind subroutineKind) :
        Symbol(SymbolKind::Subroutine, name, loc), Scope(compilation, this),
        declaredReturnType(*this), defaultLifetime(defaultLifetime),
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

    const Statement& getBody() const;
    const Type& getReturnType() const { return declaredReturnType.getType(); }

    void setOverride(const SubroutineSymbol& parentMethod) const;
    const SubroutineSymbol* getOverride() const { return overrides; }

    const MethodPrototypeSymbol* getPrototype() const { return prototype; }
    void connectExternInterfacePrototype() const;

    bool isVirtual() const {
        return flags.has(MethodFlags::Virtual | MethodFlags::Extends) || overrides != nullptr;
    }

    void serializeTo(ASTSerializer& serializer) const;

    static SubroutineSymbol* fromSyntax(Compilation& compilation,
                                        const syntax::FunctionDeclarationSyntax& syntax,
                                        const Scope& parent, bool outOfBlock);

    static SubroutineSymbol* fromSyntax(Compilation& compilation,
                                        const syntax::ClassMethodDeclarationSyntax& syntax,
                                        const Scope& parent);

    static SubroutineSymbol& fromSyntax(Compilation& compilation,
                                        const syntax::DPIImportSyntax& syntax, const Scope& parent);

    static SubroutineSymbol& createOutOfBlock(Compilation& compilation,
                                              const syntax::FunctionDeclarationSyntax& syntax,
                                              const MethodPrototypeSymbol& prototype,
                                              const Scope& newParent, const Scope& definitionScope,
                                              SymbolIndex outOfBlockIndex);

    static SubroutineSymbol& createFromPrototype(Compilation& compilation,
                                                 const MethodPrototypeSymbol& prototype,
                                                 const Scope& parent);

    static void inheritDefaultedArgList(Scope& scope, const Scope& parentScope,
                                        const syntax::SyntaxNode& syntax,
                                        SmallVectorBase<const FormalArgumentSymbol*>& arguments);

    static bitmask<MethodFlags> buildArguments(
        Scope& scope, const Scope& parentScope, const syntax::FunctionPortListSyntax& syntax,
        VariableLifetime defaultLifetime, SmallVectorBase<const FormalArgumentSymbol*>& arguments);

    static void checkVirtualMethodMatch(const Scope& scope, const SubroutineSymbol& parentMethod,
                                        const SubroutineSymbol& derivedMethod,
                                        bool allowDerivedReturn);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Subroutine; }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const;

private:
    void addThisVar(const Type& type);

    std::span<const StatementBlockSymbol* const> blocks;
    mutable const Statement* stmt = nullptr;
    ArgList arguments;
    mutable const SubroutineSymbol* overrides = nullptr;
    mutable const MethodPrototypeSymbol* prototype = nullptr;
    mutable std::optional<bool> cachedHasOutputArgs;
    mutable bool isConstructing = false;
};

class SLANG_EXPORT MethodPrototypeSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredReturnType;
    SubroutineKind subroutineKind;
    Visibility visibility;
    bitmask<MethodFlags> flags;

    MethodPrototypeSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                          SubroutineKind subroutineKind, Visibility visibility,
                          bitmask<MethodFlags> flags);

    std::span<const FormalArgumentSymbol* const> getArguments() const { return arguments; }
    const Type& getReturnType() const { return declaredReturnType.getType(); }
    const SubroutineSymbol* getSubroutine() const;

    void setOverride(const Symbol& overrideTarget) const { overrides = &overrideTarget; }
    const Symbol* getOverride() const { return overrides; }

    bool isVirtual() const {
        return flags.has(MethodFlags::Virtual | MethodFlags::Extends) || overrides != nullptr;
    }

    bool checkMethodMatch(const Scope& scope, const SubroutineSymbol& method) const;

    class ExternImpl {
    public:
        not_null<const SubroutineSymbol*> impl;

        explicit ExternImpl(const SubroutineSymbol& impl) : impl(&impl) {}

        const ExternImpl* getNextImpl() const { return next; }

    private:
        friend class MethodPrototypeSymbol;
        mutable const ExternImpl* next = nullptr;
    };

    const ExternImpl* getFirstExternImpl() const { return firstExternImpl; }
    void addExternImpl(const SubroutineSymbol& impl) const;

    void serializeTo(ASTSerializer& serializer) const;

    static MethodPrototypeSymbol& fromSyntax(const Scope& scope,
                                             const syntax::ClassMethodPrototypeSyntax& syntax);
    static MethodPrototypeSymbol& fromSyntax(const Scope& scope,
                                             const syntax::ModportSubroutinePortSyntax& syntax,
                                             bool isExport);
    static MethodPrototypeSymbol& fromSyntax(const ASTContext& context,
                                             const syntax::ModportNamedPortSyntax& syntax,
                                             bool isExport);
    static MethodPrototypeSymbol& fromSyntax(const Scope& scope,
                                             const syntax::ExternInterfaceMethodSyntax& syntax);

    static MethodPrototypeSymbol& implicitExtern(const Scope& scope,
                                                 const syntax::ModportSubroutinePortSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::MethodPrototype; }

private:
    static MethodPrototypeSymbol& createForModport(const Scope& scope,
                                                   const syntax::SyntaxNode& syntax,
                                                   parsing::Token nameToken, bool isExport);

    template<typename TSyntax>
    static MethodPrototypeSymbol& createExternIfaceMethod(const Scope& scope,
                                                          const TSyntax& syntax);

    std::span<const FormalArgumentSymbol* const> arguments;
    mutable std::optional<const SubroutineSymbol*> subroutine;
    mutable const Symbol* overrides = nullptr;
    mutable bool needsMatchCheck = false;
    mutable const ExternImpl* firstExternImpl = nullptr;
};

} // namespace slang::ast
