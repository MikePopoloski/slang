//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "Binder.h"

namespace slang {

ParameterSymbol::ParameterSymbol(StringRef name, SourceLocation location, const Symbol& parent) :
    Symbol(SymbolKind::Parameter, parent, name, location) {}

VariableSymbol::VariableSymbol(Token name, const DataTypeSyntax& type, const Symbol& parent, VariableLifetime lifetime,
                               bool isConst, const ExpressionSyntax* initializer) :
    Symbol(SymbolKind::Variable, name, parent),
    lifetime(lifetime), isConst(isConst), typeSyntax(&type), initializerSyntax(initializer)
{
}

VariableSymbol::VariableSymbol(StringRef name, SourceLocation location, const TypeSymbol& type, const Symbol& parent,
                               VariableLifetime lifetime, bool isConst, const BoundExpression* initializer) :
    Symbol(SymbolKind::Variable, parent, name, location),
    lifetime(lifetime), isConst(isConst), typeSymbol(&type), initializerBound(initializer)
{
}

VariableSymbol::VariableSymbol(SymbolKind kind, StringRef name, SourceLocation location, const TypeSymbol& type,
                               const Symbol& parent, VariableLifetime lifetime, bool isConst, const BoundExpression* initializer) :
    Symbol(kind, parent, name, location),
    lifetime(lifetime), isConst(isConst), typeSymbol(&type), initializerBound(initializer)
{
}

const TypeSymbol& VariableSymbol::type() const {
    if (typeSymbol)
        return *typeSymbol;

    ASSERT(typeSyntax);
    typeSymbol = &containingScope().getType(*typeSyntax);
    return *typeSymbol;
}

const BoundExpression* VariableSymbol::initializer() const {
    if (initializerBound)
        return initializerBound;

    if (initializerSyntax)
        initializerBound = &Binder(containingScope()).bindAssignmentLikeContext(*initializerSyntax, location, type());

    return initializerBound;
}

FormalArgumentSymbol::FormalArgumentSymbol(const TypeSymbol& type, const Symbol& parent) :
    VariableSymbol(SymbolKind::FormalArgument, nullptr, SourceLocation(), type, parent)
{
}

FormalArgumentSymbol::FormalArgumentSymbol(StringRef name, SourceLocation location, const TypeSymbol& type,
                                           const Symbol& parent, const BoundExpression* initializer,
                                           FormalArgumentDirection direction) :
    VariableSymbol(SymbolKind::FormalArgument, name, location, type, parent, VariableLifetime::Automatic,
                   direction == FormalArgumentDirection::ConstRef, initializer),
    direction(direction)
{
}

// TODO: handle functions that don't have simple name tokens
SubroutineSymbol::SubroutineSymbol(const FunctionDeclarationSyntax& syntax, const Symbol& parent) :
    ScopeSymbol(SymbolKind::Subroutine, syntax.prototype.name.getFirstToken(), parent),
    syntax(&syntax)
{
    defaultLifetime = getLifetimeFromToken(syntax.prototype.lifetime, VariableLifetime::Automatic);
    isTask = syntax.kind == SyntaxKind::TaskDeclaration;
}

SubroutineSymbol::SubroutineSymbol(StringRef name, const TypeSymbol& returnType, ArrayRef<const FormalArgumentSymbol*> arguments,
                                   SystemFunction systemFunction, const Symbol& parent) :
    ScopeSymbol(SymbolKind::Subroutine, parent, name),
    systemFunctionKind(systemFunction), returnType_(&returnType),
    arguments_(arguments), initialized(true)
{
}

void SubroutineSymbol::init() const {
    if (initialized)
        return;
    initialized = true;

    const ScopeSymbol& parentScope = containingScope();
    const DesignRootSymbol& root = getRoot();
    const auto& proto = syntax->prototype;
    auto returnType = parentScope.getType(*proto.returnType);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;

    if (proto.portList) {
        const TypeSymbol* lastType = &root.getKnownType(SyntaxKind::LogicType);
        auto lastDirection = FormalArgumentDirection::In;

        for (const FunctionPortSyntax* portSyntax : proto.portList->ports) {
            FormalArgumentDirection direction;
            bool directionSpecified = true;
            switch (portSyntax->direction.kind) {
                case TokenKind::InputKeyword: direction = FormalArgumentDirection::In; break;
                case TokenKind::OutputKeyword: direction = FormalArgumentDirection::Out; break;
                case TokenKind::InOutKeyword: direction = FormalArgumentDirection::InOut; break;
                case TokenKind::RefKeyword:
                    if (portSyntax->constKeyword)
                        direction = FormalArgumentDirection::ConstRef;
                    else
                        direction = FormalArgumentDirection::Ref;
                    break;
                default:
                    // Otherwise, we "inherit" the previous argument
                    direction = lastDirection;
                    directionSpecified = false;
                    break;
            }

            // If we're given a type, use that. Otherwise, if we were given a
            // direction, default to logic. Otherwise, use the last type.
            const TypeSymbol* type;
            if (portSyntax->dataType)
                type = &parentScope.getType(*portSyntax->dataType);
            else if (directionSpecified)
                type = &root.getKnownType(SyntaxKind::LogicType);
            else
                type = lastType;

            const auto& declarator = portSyntax->declarator;
            const BoundExpression* initializer = nullptr;
            if (declarator.initializer) {
                initializer = &Binder(parentScope).bindAssignmentLikeContext(declarator.initializer->expr,
                                                                             declarator.name.location(), *type);
            }

            arguments.append(&root.allocate<FormalArgumentSymbol>(
                declarator.name.valueText(),
                declarator.name.location(),
                *type,
                *this,
                initializer,
                direction
                ));

            addMember(*arguments.back());

            lastDirection = direction;
            lastType = type;
        }
    }

    returnType_ = &returnType;
    body_ = &Binder(*this).bindStatementList(syntax->items);
    arguments_ = arguments.copy(root.allocator());
}

}