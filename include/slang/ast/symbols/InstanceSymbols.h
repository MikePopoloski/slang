//------------------------------------------------------------------------------
//! @file InstanceSymbols.h
//! @brief Contains instance-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Scope.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/Symbol.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Function.h"

namespace slang::ast {

class AssertionExpr;
class Definition;
class Expression;
class InstanceBodySymbol;
class InterfacePortSymbol;
class MultiPortSymbol;
class ParameterBuilder;
class ParameterSymbolBase;
class PortConnection;
class PortSymbol;
class PrimitiveSymbol;
class TimingControl;
struct HierarchyOverrideNode;

/// Common functionality for module, interface, program, and primitive instances.
class SLANG_EXPORT InstanceSymbolBase : public Symbol {
public:
    span<const int32_t> arrayPath;

    /// If this instance is part of an array, walk upward to find the array's name.
    /// Otherwise returns the name of the instance itself.
    string_view getArrayName() const;

    /// Gets the set of dimensions describing the instance array that contains this instance.
    /// If this instance is not part of an array, does not add any dimensions to the given list.
    void getArrayDimensions(SmallVectorBase<ConstantRange>& dimensions) const;

protected:
    using Symbol::Symbol;
};

class SLANG_EXPORT InstanceSymbol : public InstanceSymbolBase {
public:
    const InstanceBodySymbol& body;

    InstanceSymbol(string_view name, SourceLocation loc, InstanceBodySymbol& body);

    InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                   const Definition& definition, ParameterBuilder& paramBuilder,
                   bool isUninstantiated, bool isFromBind);

    const Definition& getDefinition() const;
    bool isModule() const;
    bool isInterface() const;

    const PortConnection* getPortConnection(const PortSymbol& port) const;
    const PortConnection* getPortConnection(const MultiPortSymbol& port) const;
    const PortConnection* getPortConnection(const InterfacePortSymbol& port) const;
    span<const PortConnection* const> getPortConnections() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets, bool isFromBind);

    static void fromFixupSyntax(Compilation& compilation, const Definition& definition,
                                const syntax::DataDeclarationSyntax& syntax,
                                const ASTContext& context, SmallVectorBase<const Symbol*>& results);

    /// Creates a default-instantiated instance of the given definition. All parameters must
    /// have defaults specified.
    static InstanceSymbol& createDefault(Compilation& compilation, const Definition& definition,
                                         const HierarchyOverrideNode* hierarchyOverrideNode);

    /// Creates a placeholder instance for a virtual interface type declaration.
    static InstanceSymbol& createVirtual(
        const ASTContext& context, SourceLocation loc, const Definition& definition,
        const syntax::ParameterValueAssignmentSyntax* paramAssignments);

    /// Creates an intentionally invalid instance by forcing all parameters to null values.
    /// This allows type checking instance members as long as they don't depend on any parameters.
    static InstanceSymbol& createInvalid(Compilation& compilation, const Definition& definition);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Instance; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const; // implementation is in ASTVisitor.h

private:
    void resolvePortConnections() const;

    mutable PointerMap* connectionMap = nullptr;
    mutable span<const PortConnection* const> connections;
};

class SLANG_EXPORT InstanceBodySymbol : public Symbol, public Scope {
public:
    /// The parent instance for which this is the body.
    const InstanceSymbol* parentInstance = nullptr;

    /// A pointer into the hierarchy override tree, if this instance or any
    /// child instances have overrides that need to be applied.
    const HierarchyOverrideNode* hierarchyOverrideNode = nullptr;

    /// A copy of all port parameter symbols used to construct the instance body.
    span<const ParameterSymbolBase* const> parameters;

    /// Indicates whether the module isn't actually instantiated in the design.
    /// This might be because it was created with invalid parameters simply to
    /// check name lookup rules but it's never actually referenced elsewhere
    /// in the user's code.
    bool isUninstantiated = false;

    /// Indicates whether this instance was created from a bind directive
    /// instead of a typical instantiation.
    bool isFromBind = false;

    InstanceBodySymbol(Compilation& compilation, const Definition& definition,
                       const HierarchyOverrideNode* hierarchyOverrideNode, bool isUninstantiated,
                       bool isFromBind);

    span<const Symbol* const> getPortList() const {
        ensureElaborated();
        return portList;
    }

    const Symbol* findPort(string_view name) const;

    const Definition& getDefinition() const { return definition; }

    bool hasSameType(const InstanceBodySymbol& other) const;

    static InstanceBodySymbol& fromDefinition(Compilation& compilation,
                                              const Definition& definition, bool isUninstantiated,
                                              const HierarchyOverrideNode* hierarchyOverrideNode);

    static InstanceBodySymbol& fromDefinition(Compilation& compilation,
                                              const Definition& definition,
                                              SourceLocation instanceLoc,
                                              ParameterBuilder& paramBuilder, bool isUninstantiated,
                                              bool isFromBind);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InstanceBody; }

private:
    friend class Scope;

    void setPorts(span<const Symbol* const> ports) const { portList = ports; }

    const Definition& definition;
    mutable span<const Symbol* const> portList;
};

class SLANG_EXPORT InstanceArraySymbol : public Symbol, public Scope {
public:
    span<const Symbol* const> elements;
    ConstantRange range;

    InstanceArraySymbol(Compilation& compilation, string_view name, SourceLocation loc,
                        span<const Symbol* const> elements, ConstantRange range) :
        Symbol(SymbolKind::InstanceArray, name, loc),
        Scope(compilation, this), elements(elements), range(range) {}

    /// If this array is part of a multidimensional array, walk upward to find
    /// the root array's name. Otherwise returns the name of this symbol itself.
    string_view getArrayName() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InstanceArray; }
};

/// Represents an instance of a definition (module / interface / program / checker)
/// that is not actually instantiated in the design. This is a placeholder
/// in the AST to record this instance and capture its port expressions.
class SLANG_EXPORT UninstantiatedDefSymbol : public Symbol {
public:
    /// The name of the definition.
    string_view definitionName;

    /// The self-determined expressions that are assigned to the parameters
    /// in the instantiation. These aren't necessarily correctly typed
    /// since we can't know the destination type of each parameter.
    span<const Expression* const> paramExpressions;

    UninstantiatedDefSymbol(string_view name, SourceLocation loc, string_view definitionName,
                            span<const Expression* const> params) :
        Symbol(SymbolKind::UninstantiatedDef, name, loc),
        definitionName(definitionName), paramExpressions(params) {}

    /// Gets the self-determined expressions that are assigned to the ports
    /// in the instantiation. These aren't necessarily correctly typed
    /// since we can't know the destination type of each port.
    span<const AssertionExpr* const> getPortConnections() const;

    /// The names of the ports that were connected in the instance. If the names
    /// are not known, because ordered connection syntax was used, the associated
    /// port name will be the empty string.
    span<string_view const> getPortNames() const;

    /// Returns true if we've determined this must be a checker instance
    /// based on the syntax used to instantiate it.
    bool isChecker() const;

    static void fromSyntax(Compilation& compilation,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets);

    static void fromSyntax(Compilation& compilation,
                           const syntax::PrimitiveInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UninstantiatedDef; }

private:
    mutable std::optional<span<const AssertionExpr* const>> ports;
    mutable span<string_view const> portNames;
    mutable bool mustBeChecker = false;
};

class SLANG_EXPORT PrimitiveInstanceSymbol : public InstanceSymbolBase {
public:
    const PrimitiveSymbol& primitiveType;

    PrimitiveInstanceSymbol(string_view name, SourceLocation loc,
                            const PrimitiveSymbol& primitiveType) :
        InstanceSymbolBase(SymbolKind::PrimitiveInstance, name, loc),
        primitiveType(primitiveType) {}

    span<const Expression* const> getPortConnections() const;
    const TimingControl* getDelay() const;
    std::pair<std::optional<DriveStrength>, std::optional<DriveStrength>> getDriveStrength() const;

    static void fromSyntax(const PrimitiveSymbol& primitive,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets);

    static void fromSyntax(const syntax::PrimitiveInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PrimitiveInstance; }

private:
    mutable std::optional<span<const Expression* const>> ports;
    mutable std::optional<const TimingControl*> delay;
};

} // namespace slang::ast
