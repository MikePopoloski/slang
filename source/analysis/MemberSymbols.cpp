//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "Binder.h"
#include "ConstantEvaluator.h"

namespace slang {

//const BoundStatement& StatementBlockSymbol::bindStatement(const StatementSyntax& syntax) {
//    return static_cast<const StatementBlockSymbol*>(this)->bindStatement(syntax);
//}
//
//const BoundStatementList& StatementBlockSymbol::bindStatementList(const SyntaxList<SyntaxNode>& items) {
//    return static_cast<const StatementBlockSymbol*>(this)->bindStatementList(items);
//}

void StatementBlockSymbol::findChildSymbols(MemberBuilder& builder, const SyntaxList<SyntaxNode>& items) const {
    for (auto item : items) {
        if (item->kind == SyntaxKind::DataDeclaration) {
            SmallVectorSized<const VariableSymbol*, 4> symbols;
            VariableSymbol::fromSyntax(*this, item->as<DataDeclarationSyntax>(), symbols);

            for (auto symbol : symbols)
                builder.add(*symbol);
        }
        else if (isStatement(item->kind)) {
            findChildSymbols(builder, item->as<StatementSyntax>());
        }
    }
}

void StatementBlockSymbol::findChildSymbols(MemberBuilder& builder, const StatementSyntax& syntax) const {
    switch (syntax.kind) {
        case SyntaxKind::ConditionalStatement: {
            const auto& conditional = syntax.as<ConditionalStatementSyntax>();
            findChildSymbols(builder, conditional.statement);
            if (conditional.elseClause)
                findChildSymbols(builder, (const StatementSyntax&)conditional.elseClause->clause);
            break;
        }
        case SyntaxKind::ForLoopStatement: {
            // A for loop has an implicit block around it iff it has variable declarations in its initializers.
            const auto& loop = syntax.as<ForLoopStatementSyntax>();
            bool any = false;
            for (auto initializer : loop.initializers) {
                if (initializer->kind == SyntaxKind::ForVariableDeclaration) {
                    any = true;
                    break;
                }
            }

            if (any)
                builder.add(SequentialBlockSymbol::createImplicitBlock(loop, *this));
            else
                findChildSymbols(builder, loop.statement);
            break;
        }
        case SyntaxKind::SequentialBlockStatement:
            builder.add(allocate<SequentialBlockSymbol>(syntax.as<BlockStatementSyntax>(), *this));
            break;
        default:
            break;
    }
}

const BoundStatement& StatementBlockSymbol::bindStatement(const StatementSyntax& syntax) const {
    switch (syntax.kind) {
        case SyntaxKind::ReturnStatement:
            return bindReturnStatement((const ReturnStatementSyntax&)syntax);
        case SyntaxKind::ConditionalStatement:
            return bindConditionalStatement((const ConditionalStatementSyntax&)syntax);
        case SyntaxKind::ForLoopStatement:
            return bindForLoopStatement((const ForLoopStatementSyntax&)syntax);
        case SyntaxKind::ExpressionStatement:
            return bindExpressionStatement((const ExpressionStatementSyntax&)syntax);

            DEFAULT_UNREACHABLE;
    }
    return badStmt(nullptr);
}

const BoundStatementList& StatementBlockSymbol::bindStatementList(const SyntaxList<SyntaxNode>& items) const {
    SmallVectorSized<const BoundStatement*, 8> buffer;
    for (auto member : members()) {
        if (member->kind == SymbolKind::Variable)
            buffer.append(&allocate<BoundVariableDecl>(member->as<VariableSymbol>()));
    }

    for (const auto& item : items) {
        if (isStatement(item->kind))
            buffer.append(&bindStatement(item->as<StatementSyntax>()));
    }

    const DesignRootSymbol& root = getRoot();
    return root.allocate<BoundStatementList>(buffer.copy(root.allocator()));
}

BoundStatement& StatementBlockSymbol::bindReturnStatement(const ReturnStatementSyntax& syntax) const {
    auto stmtLoc = syntax.returnKeyword.location();
    const Symbol* subroutine = findAncestor(SymbolKind::Subroutine);
    if (!subroutine) {
        addError(DiagCode::ReturnNotInSubroutine, stmtLoc);
        return badStmt(nullptr);
    }

    const auto& expr = Binder(*this).bindAssignmentLikeContext(*syntax.returnValue, stmtLoc,
                                                               subroutine->as<SubroutineSymbol>().returnType());
    return allocate<BoundReturnStatement>(syntax, &expr);
}

BoundStatement& StatementBlockSymbol::bindConditionalStatement(const ConditionalStatementSyntax& syntax) const {
    ASSERT(syntax.predicate.conditions.count() == 1,
           "The &&& operator in if condition is not yet supported");
    ASSERT(!syntax.predicate.conditions[0]->matchesClause,
           "Pattern-matching is not yet supported");

    const auto& cond = Binder(*this).bindSelfDeterminedExpression(syntax.predicate.conditions[0]->expr);
    const auto& ifTrue = bindStatement(syntax.statement);
    const BoundStatement* ifFalse = nullptr;
    if (syntax.elseClause)
        ifFalse = &bindStatement(syntax.elseClause->clause.as<StatementSyntax>());

    return allocate<BoundConditionalStatement>(syntax, cond, ifTrue, ifFalse);
}

BoundStatement& StatementBlockSymbol::bindForLoopStatement(const ForLoopStatementSyntax& syntax) const {
    // TODO: initializers need better handling

    // If the initializers here involve doing variable declarations, then the spec says we create
    // an implicit sequential block and do the declaration there.
    /*BumpAllocator& alloc = getRoot().allocator();
    SequentialBlockSymbol& implicitInitBlock = *alloc.emplace<SequentialBlockSymbol>(*this);
    const auto& forVariable = syntax.initializers[0]->as<ForVariableDeclarationSyntax>();

    const auto& loopVar = *alloc.emplace<VariableSymbol>(forVariable.declarator.name, forVariable.type,
                                                         implicitInitBlock, VariableLifetime::Automatic, false,
                                                         &forVariable.declarator.initializer->expr);

    implicitInitBlock.setMember(loopVar);
    builder.add(implicitInitBlock);

    Binder binder(implicitInitBlock);
    const auto& stopExpr = binder.bindSelfDeterminedExpression(syntax.stopExpr);

    SmallVectorSized<const BoundExpression*, 2> steps;
    for (auto step : syntax.steps)
        steps.append(&binder.bindSelfDeterminedExpression(*step));

    const auto& statement = implicitInitBlock.bindStatement(syntax.statement);
    const auto& loop = allocate<BoundForLoopStatement>(syntax, stopExpr, steps.copy(getRoot().allocator()), statement);

    SmallVectorSized<const BoundStatement*, 2> blockList;
    blockList.append(&allocate<BoundVariableDecl>(loopVar));
    blockList.append(&loop);

    implicitInitBlock.setBody(allocate<BoundStatementList>(blockList.copy(getRoot().allocator())));
    return allocate<BoundSequentialBlock>(implicitInitBlock);*/

    return badStmt(nullptr);
}

BoundStatement& StatementBlockSymbol::bindExpressionStatement(const ExpressionStatementSyntax& syntax) const {
    const auto& expr = Binder(*this).bindSelfDeterminedExpression(syntax.expr);
    return allocate<BoundExpressionStatement>(syntax, expr);
}

BoundStatement& StatementBlockSymbol::badStmt(const BoundStatement* stmt) const {
    return allocate<BadBoundStatement>(stmt);
}

SequentialBlockSymbol::SequentialBlockSymbol(const Symbol& parent) :
    StatementBlockSymbol(SymbolKind::SequentialBlock, parent) {}

SequentialBlockSymbol::SequentialBlockSymbol(const BlockStatementSyntax& syntax, const Symbol& parent) :
    StatementBlockSymbol(SymbolKind::SequentialBlock, parent),
    syntax(&syntax) {}

const BoundStatement& SequentialBlockSymbol::getBody() const {
    if (!body)
        body = &bindStatementList(syntax ? syntax->items : nullptr);
    return *body;
}

SequentialBlockSymbol& SequentialBlockSymbol::createImplicitBlock(const ForLoopStatementSyntax& forLoop,
                                                                  const Symbol& parent) {
    BumpAllocator& alloc = parent.getRoot().allocator();
    SequentialBlockSymbol& block = *alloc.emplace<SequentialBlockSymbol>(parent);

    const auto& forVariable = forLoop.initializers[0]->as<ForVariableDeclarationSyntax>();
    const auto& loopVar = *alloc.emplace<VariableSymbol>(forVariable.declarator.name, forVariable.type,
                                                         block, VariableLifetime::Automatic, false,
                                                         &forVariable.declarator.initializer->expr);
    block.setMember(loopVar);
    return block;
}

void SequentialBlockSymbol::fillMembers(MemberBuilder& builder) const {
    if (syntax)
        findChildSymbols(builder, syntax->items);
}

ProceduralBlockSymbol::ProceduralBlockSymbol(const ProceduralBlockSyntax& syntax, const Symbol& parent) :
    StatementBlockSymbol(SymbolKind::ProceduralBlock, parent),
    syntax(syntax)
{
    switch (syntax.kind) {
        case SyntaxKind::AlwaysBlock: procedureKind = ProceduralBlockKind::Always; break;
        case SyntaxKind::AlwaysCombBlock: procedureKind = ProceduralBlockKind::AlwaysComb; break;
        case SyntaxKind::AlwaysLatchBlock: procedureKind = ProceduralBlockKind::AlwaysLatch; break;
        case SyntaxKind::AlwaysFFBlock: procedureKind = ProceduralBlockKind::AlwaysFF; break;
        case SyntaxKind::InitialBlock: procedureKind = ProceduralBlockKind::Initial; break;
        case SyntaxKind::FinalBlock: procedureKind = ProceduralBlockKind::Final; break;
        DEFAULT_UNREACHABLE;
    }
}

void ProceduralBlockSymbol::fillMembers(MemberBuilder& builder) const {
    body = &bindStatement(syntax.statement);
}

ExplicitImportSymbol::ExplicitImportSymbol(string_view packageName, string_view importName,
                                           SourceLocation location, const Symbol& parent) :
    Symbol(SymbolKind::ExplicitImport, parent, importName, location),
    packageName(packageName), importName(importName)
{
}

const PackageSymbol* ExplicitImportSymbol::package() const {
    importedSymbol();
    return package_;
}

const Symbol* ExplicitImportSymbol::importedSymbol() const {
    if (!initialized) {
        initialized = true;

        package_ = getRoot().findPackage(packageName);
        // TODO: errors
        if (package_)
            import = package_->lookup(importName, location, LookupKind::Direct);
    }
    return import;
}

ImplicitImportSymbol::ImplicitImportSymbol(const WildcardImportSymbol& wildcard, const Symbol& importedSymbol,
                                           const Symbol& parent) :
    Symbol(SymbolKind::ImplicitImport, parent, importedSymbol.name, wildcard.location),
    wildcard_(wildcard), import(importedSymbol)
{
}

const PackageSymbol* ImplicitImportSymbol::package() const {
    return wildcard_.package();
}

WildcardImportSymbol::WildcardImportSymbol(string_view packageName, SourceLocation location, const Symbol& parent) :
    Symbol(SymbolKind::WildcardImport, parent, /* no name */ "", location),
    packageName(packageName)
{
}

const PackageSymbol* WildcardImportSymbol::package() const {
    if (!initialized) {
        initialized = true;
        package_ = getRoot().findPackage(packageName);
    }
    return package_;
}

const ImplicitImportSymbol* WildcardImportSymbol::resolve(string_view lookupName, SourceLocation lookupLocation) const {
    if (!package())
        return nullptr;

    // TODO: errors... don't error on missing!
    auto symbol = package_->lookup(lookupName, lookupLocation, LookupKind::Direct);
    if (!symbol)
        return nullptr;

    return &allocate<ImplicitImportSymbol>(*this, *symbol, containingSymbol);
}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation location, const TypeSymbol& type,
                                 ConstantValue value, const Symbol& parent) :
    Symbol(SymbolKind::Parameter, parent, name, location),
    type_(&type), value_(std::move(value)) {}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation location, const DataTypeSyntax& typeSyntax,
                                 const ExpressionSyntax* defaultInitializer, const ExpressionSyntax* assignedValue,
                                 const ScopeSymbol* instanceScope, bool isLocalParam, bool isPortParam,
                                 const Symbol& parent) :
    Symbol(SymbolKind::Parameter, parent, name, location),
    instanceScope(instanceScope), typeSyntax(&typeSyntax),
    defaultInitializer(defaultInitializer), assignedValue(assignedValue),
    isLocal(isLocalParam), isPort(isPortParam)
{
    ASSERT(defaultInitializer || assignedValue);
    ASSERT(!assignedValue || instanceScope);
}

const ConstantValue* ParameterSymbol::defaultValue() const {
    if (!hasDefault())
        return nullptr;

    defaultType();
    return &defaultValue_;
}

const TypeSymbol* ParameterSymbol::defaultType() const {
    if (!hasDefault())
        return nullptr;

    if (!defaultType_)
        evaluate(defaultInitializer, defaultType_, defaultValue_, containingScope());

    return defaultType_;
}

const ConstantValue& ParameterSymbol::value() const {
    if (!type_)
        type();
    return value_;
}

const TypeSymbol& ParameterSymbol::type() const {
    if (!type_) {
        if (assignedValue)
            evaluate(assignedValue, type_, value_, *instanceScope);
        else {
            defaultType();
            type_ = defaultType_;
            value_ = defaultValue_;
        }
    }
    return *type_;
}

void ParameterSymbol::evaluate(const ExpressionSyntax* expr, const TypeSymbol*& determinedType,
                               ConstantValue& determinedValue, const ScopeSymbol& scope) const {
    ASSERT(expr);

    // If no type is given, infer the type from the initializer
    if (typeSyntax->kind == SyntaxKind::ImplicitType) {
        const auto& bound = Binder(scope).bindConstantExpression(*expr);
        determinedType = bound.type;
        if (!bound.bad())
            determinedValue = ConstantEvaluator().evaluateExpr(bound);
    }
    else {
        determinedType = &scope.getType(*typeSyntax);
        determinedValue = scope.evaluateConstantAndConvert(*expr, *determinedType, location);
    }
}

VariableSymbol::VariableSymbol(Token name, const DataTypeSyntax& type, const Symbol& parent, VariableLifetime lifetime,
                               bool isConst, const ExpressionSyntax* initializer) :
    Symbol(SymbolKind::Variable, name, parent),
    lifetime(lifetime), isConst(isConst), typeSyntax(&type), initializerSyntax(initializer) {}

VariableSymbol::VariableSymbol(string_view name, SourceLocation location, const TypeSymbol& type, const Symbol& parent,
                               VariableLifetime lifetime, bool isConst, const BoundExpression* initializer) :
    Symbol(SymbolKind::Variable, parent, name, location),
    lifetime(lifetime), isConst(isConst), typeSymbol(&type), initializerBound(initializer) {}

VariableSymbol::VariableSymbol(SymbolKind kind, string_view name, SourceLocation location, const TypeSymbol& type,
                               const Symbol& parent, VariableLifetime lifetime, bool isConst, const BoundExpression* initializer) :
    Symbol(kind, parent, name, location),
    lifetime(lifetime), isConst(isConst), typeSymbol(&type), initializerBound(initializer) {}

void VariableSymbol::fromSyntax(const Symbol& parent, const DataDeclarationSyntax& syntax,
                                SmallVector<const VariableSymbol*>& results) {

    const DesignRootSymbol& root = parent.getRoot();
    for (auto declarator : syntax.declarators) {
        const ExpressionSyntax* initializer = declarator->initializer ? &declarator->initializer->expr : nullptr;

        results.append(&root.allocate<VariableSymbol>(declarator->name, syntax.type, parent,
                                                      VariableLifetime::Automatic, false, initializer));
    }
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
    VariableSymbol(SymbolKind::FormalArgument, "", SourceLocation(), type, parent) {}

FormalArgumentSymbol::FormalArgumentSymbol(string_view name, SourceLocation location, const TypeSymbol& type,
                                           const Symbol& parent, const BoundExpression* initializer,
                                           FormalArgumentDirection direction) :
    VariableSymbol(SymbolKind::FormalArgument, name, location, type, parent, VariableLifetime::Automatic,
                   direction == FormalArgumentDirection::ConstRef, initializer),
    direction(direction) {}

// TODO: handle functions that don't have simple name tokens
SubroutineSymbol::SubroutineSymbol(const FunctionDeclarationSyntax& syntax, const Symbol& parent) :
    StatementBlockSymbol(SymbolKind::Subroutine, syntax.prototype.name.getFirstToken(), parent),
    syntax(&syntax)
{
    defaultLifetime = getLifetimeFromToken(syntax.prototype.lifetime, VariableLifetime::Automatic);
    isTask = syntax.kind == SyntaxKind::TaskDeclaration;
}

SubroutineSymbol::SubroutineSymbol(string_view name, const TypeSymbol& returnType, span<const FormalArgumentSymbol* const> arguments,
                                   SystemFunction systemFunction, const Symbol& parent) :
    StatementBlockSymbol(SymbolKind::Subroutine, parent, name),
    systemFunctionKind(systemFunction), returnType_(&returnType), arguments_(arguments) {}

const BoundStatementList& SubroutineSymbol::body() const {
    if (!body_)
        body_ = &bindStatementList(syntax ? syntax->items : nullptr);
    return *body_;
}

void SubroutineSymbol::fillMembers(MemberBuilder& builder) const {
    if (isSystemFunction())
        return;

    const ScopeSymbol& parentScope = containingScope();
    const DesignRootSymbol& root = getRoot();
    const auto& proto = syntax->prototype;
    const auto& returnType = parentScope.getType(*proto.returnType);

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

            builder.add(*arguments.back());

            lastDirection = direction;
            lastType = type;
        }
    }

    returnType_ = &returnType;
    arguments_ = arguments.copy(root.allocator());
    findChildSymbols(builder, syntax->items);

    // Note: call this last; binding the statements might request other members
    // of this subroutine, like the return type
    //body_ = &bindStatementList(builder, syntax->items);
}

}