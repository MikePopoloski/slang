//------------------------------------------------------------------------------
//! @file InstanceSymbols.h
//! @brief Contains instance-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTContext.h"
#include "slang/ast/Scope.h"
#include "slang/ast/Symbol.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class AssertionExpr;
class AttributeSymbol;
class CheckerSymbol;
class CheckerInstanceBodySymbol;
class ConfigBlockSymbol;
class DefinitionSymbol;
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
struct BindDirectiveInfo;
struct ConfigRule;
struct ResolvedConfig;
struct HierarchyOverrideNode;
enum class DriveStrength : int;

/// Specifies various flags that describe instance behavior.
enum class SLANG_EXPORT InstanceFlags : uint8_t {
    /// No flags specified.
    None = 0,

    /// The module isn't actually instantiated in the design.
    /// This might be because it was created with invalid parameters simply to
    /// check name lookup rules but it's never actually referenced elsewhere
    /// in the user's code.
    Uninstantiated = 1 << 0,

    /// The instance was created from a bind directive instead of a typical instantiation.
    FromBind = 1 << 1,

    /// The instance resides in a parent instance that itself is from a bind directive.
    /// This applies recursively for the entire bound hierarchy.
    ParentFromBind = 1 << 2
};
SLANG_BITMASK(InstanceFlags, ParentFromBind)

/// Common functionality for module, interface, program, and primitive instances.
class SLANG_EXPORT InstanceSymbolBase : public Symbol {
public:
    std::span<const int32_t> arrayPath;

    /// If this instance is part of an array, walk upward to find the array's name.
    /// Otherwise returns the name of the instance itself.
    std::string_view getArrayName() const;

    /// Gets the set of dimensions describing the instance array that contains this instance.
    /// If this instance is not part of an array, does not add any dimensions to the given list.
    void getArrayDimensions(SmallVectorBase<ConstantRange>& dimensions) const;

    static bool isKind(SymbolKind kind) {
        return kind == SymbolKind::Instance || kind == SymbolKind::PrimitiveInstance ||
               kind == SymbolKind::CheckerInstance;
    }

protected:
    using Symbol::Symbol;
};

/// Represents an instance of a module, interface, or program.
class SLANG_EXPORT InstanceSymbol : public InstanceSymbolBase {
public:
    const InstanceBodySymbol& body;

    /// A config rule that applies to this instance, or a pointer to
    /// the parent instance's config rule if there is one up the stack.
    const ResolvedConfig* resolvedConfig = nullptr;

    InstanceSymbol(std::string_view name, SourceLocation loc, InstanceBodySymbol& body);

    InstanceSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                   const DefinitionSymbol& definition, ParameterBuilder& paramBuilder,
                   bitmask<InstanceFlags> flags);

    const DefinitionSymbol& getDefinition() const;
    bool isModule() const;
    bool isInterface() const;
    bool isTopLevel() const;

    const PortConnection* getPortConnection(const PortSymbol& port) const;
    const PortConnection* getPortConnection(const MultiPortSymbol& port) const;
    const PortConnection* getPortConnection(const InterfacePortSymbol& port) const;
    std::span<const PortConnection* const> getPortConnections() const;

    /// If it has been determined that the body of this instance is an exact
    /// duplicate of another, this returns a pointer to the canonical copy
    /// to avoid duplicating effort visiting this instance's body again.
    /// Otherwise returns nullptr.
    const InstanceBodySymbol* getCanonicalBody() const { return canonicalBody; }

    void setCanonicalBody(const InstanceBodySymbol& newCanonical) const {
        canonicalBody = &newCanonical;
    }

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets,
                           const BindDirectiveInfo* bindInfo = nullptr,
                           const syntax::SyntaxNode* overrideSyntax = nullptr);

    static void fromFixupSyntax(Compilation& compilation, const DefinitionSymbol& definition,
                                const syntax::DataDeclarationSyntax& syntax,
                                const ASTContext& context, SmallVectorBase<const Symbol*>& results);

    /// Creates a default-instantiated instance of the given definition. All parameters must
    /// have defaults specified.
    static InstanceSymbol& createDefault(
        Compilation& compilation, const DefinitionSymbol& definition,
        const HierarchyOverrideNode* hierarchyOverrideNode = nullptr,
        const ConfigBlockSymbol* configBlock = nullptr, const ConfigRule* configRule = nullptr,
        SourceLocation locationOverride = {});

    /// Creates a placeholder instance for a virtual interface type declaration.
    static InstanceSymbol& createVirtual(
        const ASTContext& context, SourceLocation loc, const DefinitionSymbol& definition,
        const syntax::ParameterValueAssignmentSyntax* paramAssignments);

    /// Creates a default-instantiated instance of a nested definition in the provided scope.
    static Symbol& createDefaultNested(const Scope& scope,
                                       const syntax::ModuleDeclarationSyntax& syntax);

    /// Creates an intentionally invalid instance by forcing all parameters to null values.
    /// This allows type checking instance members as long as they don't depend on any parameters.
    static InstanceSymbol& createInvalid(Compilation& compilation,
                                         const DefinitionSymbol& definition);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Instance; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const; // implementation is in ASTVisitor.h

private:
    void resolvePortConnections() const;
    void connectDefaultIfacePorts() const;

    mutable PointerMap* connectionMap = nullptr;
    mutable std::span<const PortConnection* const> connections;
    mutable const InstanceBodySymbol* canonicalBody = nullptr;
};

class SLANG_EXPORT InstanceBodySymbol : public Symbol, public Scope {
public:
    /// The parent instance for which this is the body.
    const InstanceSymbol* parentInstance = nullptr;

    /// A pointer into the hierarchy override tree, if this instance or any
    /// child instances have overrides that need to be applied.
    const HierarchyOverrideNode* hierarchyOverrideNode = nullptr;

    /// Flags that describe properties of the instance.
    bitmask<InstanceFlags> flags;

    InstanceBodySymbol(Compilation& compilation, const DefinitionSymbol& definition,
                       const HierarchyOverrideNode* hierarchyOverrideNode,
                       bitmask<InstanceFlags> flags);

    std::span<const ParameterSymbolBase* const> getParameters() const {
        ensureElaborated();
        return parameters;
    }

    std::span<const Symbol* const> getPortList() const {
        ensureElaborated();
        return portList;
    }

    const Symbol* findPort(std::string_view name) const;

    const DefinitionSymbol& getDefinition() const { return definition; }

    bool hasSameType(const InstanceBodySymbol& other) const;

    static InstanceBodySymbol& fromDefinition(
        Compilation& compilation, const DefinitionSymbol& definition, SourceLocation instanceLoc,
        bitmask<InstanceFlags> flags, const HierarchyOverrideNode* hierarchyOverrideNode,
        const ConfigBlockSymbol* configBlock, const ConfigRule* configRule);

    static InstanceBodySymbol& fromDefinition(Compilation& compilation,
                                              const DefinitionSymbol& definition,
                                              SourceLocation instanceLoc,
                                              ParameterBuilder& paramBuilder,
                                              bitmask<InstanceFlags> flags);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InstanceBody; }

private:
    friend class Scope;

    void setPorts(std::span<const Symbol* const> ports) const { portList = ports; }

    const DefinitionSymbol& definition;
    mutable std::span<const Symbol* const> portList;
    std::span<const ParameterSymbolBase* const> parameters;
};

class SLANG_EXPORT InstanceArraySymbol : public Symbol, public Scope {
public:
    std::span<const Symbol* const> elements;
    ConstantRange range;

    InstanceArraySymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                        std::span<const Symbol* const> elements, ConstantRange range) :
        Symbol(SymbolKind::InstanceArray, name, loc), Scope(compilation, this), elements(elements),
        range(range) {}

    /// If this array is part of a multidimensional array, walk upward to find
    /// the root array's name. Otherwise returns the name of this symbol itself.
    std::string_view getArrayName() const;

    static InstanceArraySymbol& createEmpty(Compilation& compilation, std::string_view name,
                                            SourceLocation loc);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InstanceArray; }
};

/// Represents an instance of a definition (module / interface / program / checker)
/// that is not actually instantiated in the design. This is a placeholder
/// in the AST to record this instance and capture its port expressions.
class SLANG_EXPORT UninstantiatedDefSymbol : public Symbol {
public:
    /// The name of the definition.
    std::string_view definitionName;

    /// The self-determined expressions that are assigned to the parameters
    /// in the instantiation. These aren't necessarily correctly typed
    /// since we can't know the destination type of each parameter.
    std::span<const Expression* const> paramExpressions;

    UninstantiatedDefSymbol(std::string_view name, SourceLocation loc,
                            std::string_view definitionName,
                            std::span<const Expression* const> params) :
        Symbol(SymbolKind::UninstantiatedDef, name, loc), definitionName(definitionName),
        paramExpressions(params) {}

    /// Gets the self-determined expressions that are assigned to the ports
    /// in the instantiation. These aren't necessarily correctly typed
    /// since we can't know the destination type of each port.
    std::span<const AssertionExpr* const> getPortConnections() const;

    /// The names of the ports that were connected in the instance. If the names
    /// are not known, because ordered connection syntax was used, the associated
    /// port name will be the empty string.
    std::span<std::string_view const> getPortNames() const;

    /// Returns true if we've determined this must be a checker instance
    /// based on the syntax used to instantiate it.
    bool isChecker() const;

    static void fromSyntax(Compilation& compilation,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets);

    static void fromSyntax(Compilation& compilation,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const syntax::HierarchicalInstanceSyntax* specificInstance,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets,
                           SmallSet<std::string_view, 8>& implicitNetNames, const NetType& netType);

    static void fromSyntax(Compilation& compilation,
                           const syntax::PrimitiveInstantiationSyntax& syntax,
                           const syntax::HierarchicalInstanceSyntax* specificInstance,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets,
                           SmallSet<std::string_view, 8>& implicitNetNames);

    static void fromSyntax(Compilation& compilation,
                           const syntax::CheckerInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UninstantiatedDef; }

private:
    mutable std::optional<std::span<const AssertionExpr* const>> ports;
    mutable std::span<std::string_view const> portNames;
    mutable bool mustBeChecker = false;
};

class SLANG_EXPORT PrimitiveInstanceSymbol : public InstanceSymbolBase {
public:
    const PrimitiveSymbol& primitiveType;

    PrimitiveInstanceSymbol(std::string_view name, SourceLocation loc,
                            const PrimitiveSymbol& primitiveType) :
        InstanceSymbolBase(SymbolKind::PrimitiveInstance, name, loc), primitiveType(primitiveType) {
    }

    std::span<const Expression* const> getPortConnections() const;
    const TimingControl* getDelay() const;
    std::pair<std::optional<DriveStrength>, std::optional<DriveStrength>> getDriveStrength() const;

    static void fromSyntax(const PrimitiveSymbol& primitive,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const syntax::HierarchicalInstanceSyntax* specificInstance,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets,
                           SmallSet<std::string_view, 8>& implicitNetNames);

    static void fromSyntax(const syntax::PrimitiveInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PrimitiveInstance; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const; // implementation is in ASTVisitor.h

private:
    mutable std::optional<std::span<const Expression* const>> ports;
    mutable std::optional<const TimingControl*> delay;
};

class SLANG_EXPORT CheckerInstanceSymbol : public InstanceSymbolBase {
public:
    const CheckerInstanceBodySymbol& body;

    CheckerInstanceSymbol(std::string_view name, SourceLocation loc,
                          CheckerInstanceBodySymbol& body);

    class SLANG_EXPORT Connection {
    public:
        const CheckerInstanceBodySymbol& parent;
        const Symbol& formal;
        std::variant<const Expression*, const AssertionExpr*, const TimingControl*> actual;
        std::span<const AttributeSymbol* const> attributes;

        Connection(const CheckerInstanceBodySymbol& parent, const Symbol& formal,
                   const syntax::ExpressionSyntax* outputInitialSyntax,
                   std::span<const AttributeSymbol* const> attributes) :
            parent(parent), formal(formal), attributes(attributes),
            outputInitialSyntax(outputInitialSyntax) {}

        const Expression* getOutputInitialExpr() const;

    private:
        const syntax::ExpressionSyntax* outputInitialSyntax;
        mutable std::optional<const Expression*> outputInitialExpr;
    };

    std::span<const Connection> getPortConnections() const;

    static void fromSyntax(const CheckerSymbol& checker,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets,
                           bitmask<InstanceFlags> flags);

    static void fromSyntax(const syntax::CheckerInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets,
                           bitmask<InstanceFlags> flags);

    /// Creates an intentionally invalid instance by forcing all port connections to
    /// null values. This allows type checking instance members as long as they don't
    /// depend on any port expansion.
    static CheckerInstanceSymbol& createInvalid(const CheckerSymbol& checker, uint32_t depth);

    static CheckerInstanceSymbol& fromSyntax(
        Compilation& compilation, const ASTContext& context, const CheckerSymbol& checker,
        const syntax::HierarchicalInstanceSyntax& syntax,
        std::span<const syntax::AttributeInstanceSyntax* const> attributes,
        SmallVectorBase<int32_t>& path, bool isProcedural, bitmask<InstanceFlags> flags);

    void verifyMembers() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CheckerInstance; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const; // implementation is in ASTVisitor.h

private:
    std::span<Connection> connections;
    mutable bool connectionsResolved = false;
};

class SLANG_EXPORT CheckerInstanceBodySymbol : public Symbol, public Scope {
public:
    /// The parent instance for which this is the body.
    const CheckerInstanceSymbol* parentInstance = nullptr;

    const CheckerSymbol& checker;
    const AssertionInstanceDetails& assertionDetails;
    uint32_t instanceDepth;
    bool isProcedural;
    bitmask<InstanceFlags> flags;

    CheckerInstanceBodySymbol(Compilation& compilation, const CheckerSymbol& checker,
                              AssertionInstanceDetails& assertionDetails,
                              const ASTContext& originalContext, uint32_t instanceDepth,
                              bool isProcedural, bitmask<InstanceFlags> flags);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CheckerInstanceBody; }

private:
    ASTContext originalContext;
};

} // namespace slang::ast
