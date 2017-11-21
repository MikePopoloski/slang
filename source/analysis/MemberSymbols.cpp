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

SequentialBlockSymbol::SequentialBlockSymbol(const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::SequentialBlock, parent),
    body(this)
{
}

SequentialBlockSymbol& SequentialBlockSymbol::createImplicitBlock(const ForLoopStatementSyntax& forLoop,
                                                                  const ScopeSymbol& parent) {
    BumpAllocator& alloc = parent.getRoot().allocator();
    SequentialBlockSymbol& block = *alloc.emplace<SequentialBlockSymbol>(parent);

    const auto& forVariable = forLoop.initializers[0]->as<ForVariableDeclarationSyntax>();
    auto& loopVar = *alloc.emplace<VariableSymbol>(forVariable.declarator.name.valueText(), block);
    loopVar.type = forVariable.type;
    loopVar.initializer = forVariable.declarator.initializer->expr;

    block.setMember(loopVar);
    return block;
}

ProceduralBlockSymbol::ProceduralBlockSymbol(const ScopeSymbol& parent, ProceduralBlockKind procedureKind) :
    ScopeSymbol(SymbolKind::ProceduralBlock, parent),
    body(this),
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

ParameterSymbol::ParameterSymbol(string_view name, const ScopeSymbol& parent) :
    Symbol(SymbolKind::Parameter, parent, name),
    defaultValue(getParent()),
    value(getParent())
{
}

void ParameterSymbol::fromSyntax(SymbolFactory& factory, const ParameterDeclarationSyntax& syntax,
                                 const ScopeSymbol& parent, SmallVector<ParameterSymbol*>& results) {

    bool isLocal = syntax.keyword.kind == TokenKind::LocalParamKeyword;

    for (const VariableDeclaratorSyntax* decl : syntax.declarators) {
        auto param = factory.alloc.emplace<ParameterSymbol>(decl->name.valueText(), parent);
        param->isLocalParam = isLocal;

        if (decl->initializer) {
            param->defaultValue = decl->initializer->expr;
            param->value = param->defaultValue;
        }

        // TODO: handle defaultType

            // TODO:
           /* else if (local)
                addError(DiagCode::LocalParamNoInitializer, declLocation);
            else if (bodyParam)
                addError(DiagCode::BodyParamNoInitializer, declLocation);*/

        results.append(param);
    }
}

// TODO:
//void ParameterSymbol::evaluate(const ExpressionSyntax* expr, const TypeSymbol*& determinedType,
//                               ConstantValue*& determinedValue, const ScopeSymbol& scope) const {
//    ASSERT(expr);
//
//    // If no type is given, infer the type from the initializer
//    if (typeSyntax->kind == SyntaxKind::ImplicitType) {
//        const auto& bound = Binder(scope).bindConstantExpression(*expr);
//        determinedType = bound.type;
//        if (!bound.bad())
//            determinedValue = getRoot().constantAllocator.emplace(bound.eval());
//    }
//    else {
//        determinedType = &getRoot().factory.getType(*typeSyntax, scope);
//        determinedValue = getRoot().constantAllocator.emplace(scope.evaluateConstantAndConvert(*expr, *determinedType, location));
//    }
//}

VariableSymbol::VariableSymbol(string_view name, const ScopeSymbol& parent,
                               VariableLifetime lifetime, bool isConst) :
    Symbol(SymbolKind::Variable, parent, name),
    type(&parent), initializer(&parent),
    lifetime(lifetime), isConst(isConst) {}

VariableSymbol::VariableSymbol(SymbolKind kind, string_view name, const ScopeSymbol& parent,
                               VariableLifetime lifetime, bool isConst) :
    Symbol(kind, parent, name),
    type(&parent), initializer(&parent),
    lifetime(lifetime), isConst(isConst) {}

void VariableSymbol::fromSyntax(const ScopeSymbol& parent, const DataDeclarationSyntax& syntax,
                                SmallVector<const VariableSymbol*>& results) {

    const RootSymbol& root = parent.getRoot();
    for (auto declarator : syntax.declarators) {
        auto& variable = root.allocate<VariableSymbol>(declarator->name.valueText(), parent);
        variable.type = syntax.type;
        if (declarator->initializer)
            variable.initializer = declarator->initializer->expr;

        results.append(&variable);
    }
}

FormalArgumentSymbol::FormalArgumentSymbol(const ScopeSymbol& parent) :
    VariableSymbol(SymbolKind::FormalArgument, "", parent) {}

FormalArgumentSymbol::FormalArgumentSymbol(string_view name, const ScopeSymbol& parent,
                                           FormalArgumentDirection direction) :
    VariableSymbol(SymbolKind::FormalArgument, name, parent, VariableLifetime::Automatic,
                   direction == FormalArgumentDirection::ConstRef),
    direction(direction) {}

SubroutineSymbol::SubroutineSymbol(string_view name, VariableLifetime defaultLifetime,
                                   bool isTask, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::Subroutine, parent, name),
    body(this), returnType(this),
    defaultLifetime(defaultLifetime), isTask(isTask)
{
}

// TODO: move these someplace better

static void findChildSymbols(const ScopeSymbol& parent, const StatementSyntax& syntax,
                             SmallVector<const Symbol*>& results) {
    switch (syntax.kind) {
        case SyntaxKind::ConditionalStatement: {
            const auto& conditional = syntax.as<ConditionalStatementSyntax>();
            findChildSymbols(parent, conditional.statement, results);
            if (conditional.elseClause)
                findChildSymbols(parent, conditional.elseClause->clause.as<StatementSyntax>(), results);
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
                results.append(&SequentialBlockSymbol::createImplicitBlock(loop, parent));
            else
                findChildSymbols(parent, loop.statement, results);
            break;
        }
        case SyntaxKind::SequentialBlockStatement: {
            auto block = &parent.getRoot().allocate<SequentialBlockSymbol>(parent);
            // TODO: set children
            results.append(block);
            break;
        }
        default:
            break;
    }
}

static void findChildSymbols(const ScopeSymbol& parent, const SyntaxList<SyntaxNode>& items,
                             SmallVector<const Symbol*>& results) {
    for (auto item : items) {
        if (item->kind == SyntaxKind::DataDeclaration) {
            SmallVectorSized<const VariableSymbol*, 4> symbols;
            VariableSymbol::fromSyntax(parent, item->as<DataDeclarationSyntax>(), symbols);
            results.appendRange(symbols);
        }
        else if (isStatement(item->kind)) {
            findChildSymbols(parent, item->as<StatementSyntax>(), results);
        }
    }
}

SubroutineSymbol::SubroutineSymbol(string_view name, SystemFunction systemFunction, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::Subroutine, parent, name),
    body(this), returnType(this),
    systemFunctionKind(systemFunction) {}

SubroutineSymbol& SubroutineSymbol::fromSyntax(SymbolFactory& factory, const FunctionDeclarationSyntax& syntax,
                                               const ScopeSymbol& parent) {
    // TODO: non simple names?
    const auto& proto = syntax.prototype;
    auto result = factory.alloc.emplace<SubroutineSymbol>(
        proto.name.getFirstToken().valueText(),
        SemanticFacts::getVariableLifetime(proto.lifetime).value_or(VariableLifetime::Automatic),
        syntax.kind == SyntaxKind::TaskDeclaration,
        parent
    );

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto.portList) {
        const DataTypeSyntax* lastType = nullptr;
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

            const auto& declarator = portSyntax->declarator;
            auto arg = factory.alloc.emplace<FormalArgumentSymbol>(declarator.name.valueText(),
                                                                   *result, direction);

            // If we're given a type, use that. Otherwise, if we were given a
            // direction, default to logic. Otherwise, use the last type.
            if (portSyntax->dataType) {
                arg->type = *portSyntax->dataType;
                lastType = portSyntax->dataType;
            }
            else if (directionSpecified || !lastType) {
                arg->type = factory.getLogicType();
                lastType = nullptr;
            }
            else {
                arg->type = *lastType;
            }

            if (declarator.initializer)
                arg->initializer = declarator.initializer->expr;

            arguments.append(arg);
            lastDirection = direction;
        }
    }

    // TODO: mising return type
    result->arguments = arguments.copy(factory.alloc);
    result->returnType = *proto.returnType;
    result->body = syntax.items;

    // TODO: clean this up
    SmallVectorSized<const Symbol*, 8> members;
    for (auto arg : arguments)
        members.append(arg);

    findChildSymbols(*result, syntax.items, members);

    result->setMembers(members);

    return *result;
}

}
