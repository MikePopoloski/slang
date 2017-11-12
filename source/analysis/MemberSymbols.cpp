//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "Binder.h"
#include "RootSymbol.h"

namespace slang {

void BlockSymbol::findChildSymbols(MemberBuilder& builder, const SyntaxList<SyntaxNode>& items) const {
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

void BlockSymbol::findChildSymbols(MemberBuilder& builder, const StatementSyntax& syntax) const {
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
            builder.add(getRoot().allocate<SequentialBlockSymbol>(*this));
            break;
        default:
            break;
    }
}

const Statement& BlockSymbol::bindStatement(const StatementSyntax& syntax) const {
    switch (syntax.kind) {
        case SyntaxKind::ReturnStatement:
            return bindReturnStatement((const ReturnStatementSyntax&)syntax);
        case SyntaxKind::ConditionalStatement:
            return bindConditionalStatement((const ConditionalStatementSyntax&)syntax);
        case SyntaxKind::ForLoopStatement:
            return bindForLoopStatement((const ForLoopStatementSyntax&)syntax);
        case SyntaxKind::ExpressionStatement:
            return bindExpressionStatement((const ExpressionStatementSyntax&)syntax);
        default: THROW_UNREACHABLE;
    }
}

const StatementList& BlockSymbol::bindStatementList(const SyntaxList<SyntaxNode>& items) const {
    SmallVectorSized<const Statement*, 8> buffer;
    for (auto member : members()) {
        if (member->kind == SymbolKind::Variable)
            buffer.append(&getRoot().allocate<VariableDeclStatement>(member->as<VariableSymbol>()));
    }

    for (const auto& item : items) {
        if (isStatement(item->kind))
            buffer.append(&bindStatement(item->as<StatementSyntax>()));
    }

    const RootSymbol& root = getRoot();
    return root.allocate<StatementList>(buffer.copy(root.allocator()));
}

Statement& BlockSymbol::bindReturnStatement(const ReturnStatementSyntax& syntax) const {
    auto stmtLoc = syntax.returnKeyword.location();
    const Symbol* subroutine = findAncestor(SymbolKind::Subroutine);
    if (!subroutine) {
        addError(DiagCode::ReturnNotInSubroutine, stmtLoc);
        return badStmt(nullptr);
    }

    const auto& expr = Binder(*this).bindAssignmentLikeContext(*syntax.returnValue, stmtLoc,
                                                               subroutine->as<SubroutineSymbol>().returnType());
    return getRoot().allocate<ReturnStatement>(syntax, &expr);
}

Statement& BlockSymbol::bindConditionalStatement(const ConditionalStatementSyntax& syntax) const {
    ASSERT(syntax.predicate.conditions.count() == 1);
    ASSERT(!syntax.predicate.conditions[0]->matchesClause);

    const auto& cond = Binder(*this).bindSelfDeterminedExpression(syntax.predicate.conditions[0]->expr);
    const auto& ifTrue = bindStatement(syntax.statement);
    const Statement* ifFalse = nullptr;
    if (syntax.elseClause)
        ifFalse = &bindStatement(syntax.elseClause->clause.as<StatementSyntax>());

    return getRoot().allocate<ConditionalStatement>(syntax, cond, ifTrue, ifFalse);
}

Statement& BlockSymbol::bindForLoopStatement(const ForLoopStatementSyntax&) const {
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

    SmallVectorSized<const Statement*, 2> blockList;
    blockList.append(&allocate<BoundVariableDecl>(loopVar));
    blockList.append(&loop);

    implicitInitBlock.setBody(allocate<StatementList>(blockList.copy(getRoot().allocator())));
    return allocate<BoundSequentialBlock>(implicitInitBlock);*/

    return badStmt(nullptr);
}

Statement& BlockSymbol::bindExpressionStatement(const ExpressionStatementSyntax& syntax) const {
    const auto& expr = Binder(*this).bindSelfDeterminedExpression(syntax.expr);
    return getRoot().allocate<ExpressionStatement>(syntax, expr);
}

Statement& BlockSymbol::badStmt(const Statement* stmt) const {
    return getRoot().allocate<InvalidStatement>(stmt);
}

SequentialBlockSymbol::SequentialBlockSymbol(const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::SequentialBlock, parent) {}

SequentialBlockSymbol& SequentialBlockSymbol::createImplicitBlock(const ForLoopStatementSyntax& forLoop,
                                                                  const ScopeSymbol& parent) {
    BumpAllocator& alloc = parent.getRoot().allocator();
    SequentialBlockSymbol& block = *alloc.emplace<SequentialBlockSymbol>(parent);

    const auto& forVariable = forLoop.initializers[0]->as<ForVariableDeclarationSyntax>();
    const auto& loopVar = *alloc.emplace<VariableSymbol>(forVariable.declarator.name, forVariable.type,
                                                         block, VariableLifetime::Automatic, false,
                                                         &forVariable.declarator.initializer->expr);
    block.setMember(loopVar);
    return block;
}

ProceduralBlockSymbol::ProceduralBlockSymbol(const ScopeSymbol& parent, ProceduralBlockKind procedureKind) :
    ScopeSymbol(SymbolKind::ProceduralBlock, parent),
    procedureKind(procedureKind)
{
}

ExplicitImportSymbol::ExplicitImportSymbol(string_view packageName, string_view importName,
                                           SourceLocation location, const ScopeSymbol& parent) :
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
                                           const ScopeSymbol& parent) :
    Symbol(SymbolKind::ImplicitImport, parent, importedSymbol.name, wildcard.location),
    wildcard_(wildcard), import(importedSymbol)
{
}

const PackageSymbol* ImplicitImportSymbol::package() const {
    return wildcard_.package();
}

WildcardImportSymbol::WildcardImportSymbol(string_view packageName, SourceLocation location, const ScopeSymbol& parent) :
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

    return &getRoot().allocate<ImplicitImportSymbol>(*this, *symbol, *getParent());
}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation location, const TypeSymbol& type,
                                 ConstantValue value, const ScopeSymbol& parent) :
    Symbol(SymbolKind::Parameter, parent, name, location),
    type_(&type)
{
    value_ = getRoot().constantAllocator.emplace(std::move(value));
}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation location, const DataTypeSyntax& typeSyntax,
                                 const ExpressionSyntax* defaultInitializer, const ExpressionSyntax* assignedValue,
                                 const ScopeSymbol* instanceScope, bool isLocalParam, bool isPortParam,
                                 const ScopeSymbol& parent) :
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
    return defaultValue_;
}

const TypeSymbol* ParameterSymbol::defaultType() const {
    if (!hasDefault())
        return nullptr;

    if (!defaultType_)
        evaluate(defaultInitializer, defaultType_, defaultValue_, *getParent());

    return defaultType_;
}

const ConstantValue& ParameterSymbol::value() const {
    if (!type_)
        type();
    return *value_;
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
                               ConstantValue*& determinedValue, const ScopeSymbol& scope) const {
    ASSERT(expr);

    // If no type is given, infer the type from the initializer
    if (typeSyntax->kind == SyntaxKind::ImplicitType) {
        const auto& bound = Binder(scope).bindConstantExpression(*expr);
        determinedType = bound.type;
        if (!bound.bad())
            determinedValue = getRoot().constantAllocator.emplace(bound.eval());
    }
    else {
        determinedType = &getRoot().factory.getType(*typeSyntax, scope);
        determinedValue = getRoot().constantAllocator.emplace(scope.evaluateConstantAndConvert(*expr, *determinedType, location));
    }
}

VariableSymbol::VariableSymbol(Token name, const DataTypeSyntax& type, const ScopeSymbol& parent, VariableLifetime lifetime,
                               bool isConst, const ExpressionSyntax* initializer) :
    Symbol(SymbolKind::Variable, name, parent),
    lifetime(lifetime), isConst(isConst), typeSyntax(&type), initializerSyntax(initializer) {}

VariableSymbol::VariableSymbol(string_view name, SourceLocation location, const TypeSymbol& type, const ScopeSymbol& parent,
                               VariableLifetime lifetime, bool isConst, const Expression* initializer) :
    Symbol(SymbolKind::Variable, parent, name, location),
    lifetime(lifetime), isConst(isConst), typeSymbol(&type), initializerBound(initializer) {}

VariableSymbol::VariableSymbol(SymbolKind kind, string_view name, SourceLocation location, const TypeSymbol& type,
                               const ScopeSymbol& parent, VariableLifetime lifetime, bool isConst, const Expression* initializer) :
    Symbol(kind, parent, name, location),
    lifetime(lifetime), isConst(isConst), typeSymbol(&type), initializerBound(initializer) {}

void VariableSymbol::fromSyntax(const ScopeSymbol& parent, const DataDeclarationSyntax& syntax,
                                SmallVector<const VariableSymbol*>& results) {

    const RootSymbol& root = parent.getRoot();
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
    typeSymbol = &getRoot().factory.getType(*typeSyntax, *getParent());
    return *typeSymbol;
}

const Expression* VariableSymbol::initializer() const {
    if (initializerBound)
        return initializerBound;

    if (initializerSyntax)
        initializerBound = &Binder(*getParent()).bindAssignmentLikeContext(*initializerSyntax, location, type());

    return initializerBound;
}

FormalArgumentSymbol::FormalArgumentSymbol(const TypeSymbol& type, const ScopeSymbol& parent) :
    VariableSymbol(SymbolKind::FormalArgument, "", SourceLocation(), type, parent) {}

FormalArgumentSymbol::FormalArgumentSymbol(string_view name, SourceLocation location, const TypeSymbol& type,
                                           const ScopeSymbol& parent, const Expression* initializer,
                                           FormalArgumentDirection direction) :
    VariableSymbol(SymbolKind::FormalArgument, name, location, type, parent, VariableLifetime::Automatic,
                   direction == FormalArgumentDirection::ConstRef, initializer),
    direction(direction) {}

// TODO: handle functions that don't have simple name tokens
SubroutineSymbol::SubroutineSymbol(const FunctionDeclarationSyntax& syntax, const ScopeSymbol& parent) :
    BlockSymbol(SymbolKind::Subroutine, syntax.prototype.name.getFirstToken(), parent),
    syntax(&syntax)
{
    defaultLifetime = SemanticFacts::getVariableLifetime(syntax.prototype.lifetime).value_or(VariableLifetime::Automatic);
    isTask = syntax.kind == SyntaxKind::TaskDeclaration;
}

SubroutineSymbol::SubroutineSymbol(string_view name, const TypeSymbol& returnType, span<const FormalArgumentSymbol* const> arguments,
                                   SystemFunction systemFunction, const ScopeSymbol& parent) :
    BlockSymbol(SymbolKind::Subroutine, parent, name),
    systemFunctionKind(systemFunction), returnType_(&returnType), arguments_(arguments) {}

const StatementList& SubroutineSymbol::body() const {
    if (!body_)
        body_ = &bindStatementList(syntax ? syntax->items : nullptr);
    return *body_;
}

void SubroutineSymbol::fillMembers(MemberBuilder& builder) const {
    if (isSystemFunction())
        return;

    const ScopeSymbol& parent = *getParent();
    const RootSymbol& root = getRoot();
    const auto& proto = syntax->prototype;
    const auto& returnType = getRoot().factory.getType(*proto.returnType, parent);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;

    if (proto.portList) {
        const TypeSymbol* lastType = &root.factory.getLogicType();
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
                case TokenKind::Unknown:
                    // Otherwise, we "inherit" the previous argument
                    direction = lastDirection;
                    directionSpecified = false;
                    break;
                default: THROW_UNREACHABLE;
            }

            // If we're given a type, use that. Otherwise, if we were given a
            // direction, default to logic. Otherwise, use the last type.
            const TypeSymbol* type;
            if (portSyntax->dataType)
                type = &root.factory.getType(*portSyntax->dataType, parent);
            else if (directionSpecified)
                type = &root.factory.getLogicType();
            else
                type = lastType;

            const auto& declarator = portSyntax->declarator;
            const Expression* initializer = nullptr;
            if (declarator.initializer) {
                initializer = &Binder(parent).bindAssignmentLikeContext(declarator.initializer->expr,
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
