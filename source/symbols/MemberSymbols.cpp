//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/MemberSymbols.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

namespace slang {

EmptyMemberSymbol& EmptyMemberSymbol::fromSyntax(Compilation& compilation, const Scope& scope,
                                                 const EmptyMemberSyntax& syntax) {
    auto result = compilation.emplace<EmptyMemberSymbol>(syntax.semi.location());

    result->setAttributes(scope, syntax.attributes);
    if (syntax.attributes.empty())
        scope.addDiag(diag::EmptyMember, syntax.sourceRange());

    return *result;
}

const PackageSymbol* ExplicitImportSymbol::package() const {
    importedSymbol();
    return package_;
}

const Symbol* ExplicitImportSymbol::importedSymbol() const {
    if (!initialized) {
        initialized = true;

        const Scope* scope = getParentScope();
        ASSERT(scope);

        if (packageName.empty())
            return nullptr;

        package_ = scope->getCompilation().getPackage(packageName);
        if (!package_) {
            auto loc = location;
            if (auto syntax = getSyntax(); syntax)
                loc = syntax->as<PackageImportItemSyntax>().package.location();

            scope->addDiag(diag::UnknownPackage, loc) << packageName;
        }
        else if (importName.empty()) {
            return nullptr;
        }
        else {
            import = package_->find(importName);
            if (!import) {
                auto loc = location;
                if (auto syntax = getSyntax())
                    loc = syntax->as<PackageImportItemSyntax>().item.location();

                auto& diag = scope->addDiag(diag::UnknownPackageMember, loc);
                diag << importName << packageName;
            }
        }
    }
    return import;
}

void ExplicitImportSymbol::serializeTo(ASTSerializer& serializer) const {
    if (auto pkg = package())
        serializer.writeLink("package", *pkg);

    if (auto sym = importedSymbol())
        serializer.writeLink("import", *sym);
}

const PackageSymbol* WildcardImportSymbol::getPackage() const {
    if (!package) {
        const Scope* scope = getParentScope();
        ASSERT(scope);

        if (packageName.empty()) {
            package = nullptr;
        }
        else {
            package = scope->getCompilation().getPackage(packageName);
            if (!package.value()) {
                auto loc = location;
                if (auto syntax = getSyntax(); syntax)
                    loc = syntax->as<PackageImportItemSyntax>().package.location();

                scope->addDiag(diag::UnknownPackage, loc) << packageName;
            }
        }
    }
    return *package;
}

void WildcardImportSymbol::serializeTo(ASTSerializer& serializer) const {
    if (auto pkg = getPackage())
        serializer.writeLink("package", *pkg);
}

const Statement& SubroutineSymbol::getBody(EvalContext* evalContext) const {
    BindContext context(*this, LookupLocation::max, BindFlags::ProceduralStatement);
    context.evalContext = evalContext;
    return binder.getStatement(context);
}

SubroutineSymbol& SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const FunctionDeclarationSyntax& syntax,
                                               const Scope& parent) {
    // TODO: non simple names?
    auto proto = syntax.prototype;
    Token nameToken = proto->name->getFirstToken();
    auto lifetime = SemanticFacts::getVariableLifetime(proto->lifetime);
    if (!lifetime.has_value())
        lifetime = parent.getDefaultLifetime();

    auto subroutineKind = syntax.kind == SyntaxKind::TaskDeclaration ? SubroutineKind::Task
                                                                     : SubroutineKind::Function;
    auto result = compilation.emplace<SubroutineSymbol>(compilation, nameToken.valueText(),
                                                        nameToken.location(), *lifetime,
                                                        subroutineKind, parent);

    result->setSyntax(syntax);
    result->setAttributes(parent, syntax.attributes);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto->portList) {
        const DataTypeSyntax* lastType = nullptr;
        auto lastDirection = ArgumentDirection::In;

        for (const FunctionPortSyntax* portSyntax : proto->portList->ports) {
            ArgumentDirection direction;
            bool directionSpecified = true;
            switch (portSyntax->direction.kind) {
                case TokenKind::InputKeyword:
                    direction = ArgumentDirection::In;
                    break;
                case TokenKind::OutputKeyword:
                    direction = ArgumentDirection::Out;
                    break;
                case TokenKind::InOutKeyword:
                    direction = ArgumentDirection::InOut;
                    break;
                case TokenKind::RefKeyword:
                    if (portSyntax->constKeyword)
                        direction = ArgumentDirection::ConstRef;
                    else
                        direction = ArgumentDirection::Ref;
                    break;
                case TokenKind::Unknown:
                    // Otherwise, we "inherit" the previous argument
                    direction = lastDirection;
                    directionSpecified = false;
                    break;
                default:
                    THROW_UNREACHABLE;
            }

            auto declarator = portSyntax->declarator;
            auto arg = compilation.emplace<FormalArgumentSymbol>(
                declarator->name.valueText(), declarator->name.location(), direction);

            // If we're given a type, use that. Otherwise, if we were given a
            // direction, default to logic. Otherwise, use the last type.
            if (portSyntax->dataType) {
                arg->setDeclaredType(*portSyntax->dataType);
                lastType = portSyntax->dataType;
            }
            else if (directionSpecified || !lastType) {
                arg->setType(compilation.getLogicType());
                lastType = nullptr;
            }
            else {
                arg->setDeclaredType(*lastType);
            }

            arg->setFromDeclarator(*declarator);
            arg->setAttributes(*result, portSyntax->attributes);

            result->addMember(*arg);
            arguments.append(arg);
            lastDirection = direction;
        }
    }

    // Subroutines can also declare arguments inside their bodies as port declarations.
    // Let's go looking for them. They're required to be declared before any other statements.
    bool portListError = false;
    for (auto item : syntax.items) {
        if (StatementSyntax::isKind(item->kind))
            break;

        if (item->kind != SyntaxKind::PortDeclaration)
            continue;

        auto& portDecl = item->as<PortDeclarationSyntax>();
        if (portDecl.header->kind != SyntaxKind::VariablePortHeader) {
            parent.addDiag(diag::ExpectedFunctionPort, portDecl.header->sourceRange());
            continue;
        }

        if (!portListError && proto->portList) {
            auto& diag = parent.addDiag(diag::MixingSubroutinePortKinds, portDecl.sourceRange());
            diag.addNote(diag::NoteDeclarationHere, proto->portList->getFirstToken().location());
            portListError = true;
        }

        // TODO: const ref is not currently handled by parser
        auto& header = portDecl.header->as<VariablePortHeaderSyntax>();
        ArgumentDirection direction;
        switch (header.direction.kind) {
            case TokenKind::InputKeyword:
                direction = ArgumentDirection::In;
                break;
            case TokenKind::OutputKeyword:
                direction = ArgumentDirection::Out;
                break;
            case TokenKind::InOutKeyword:
                direction = ArgumentDirection::InOut;
                break;
            case TokenKind::RefKeyword:
                direction = ArgumentDirection::Ref;
                break;
            default:
                THROW_UNREACHABLE;
        }

        for (auto declarator : portDecl.declarators) {
            auto arg = compilation.emplace<FormalArgumentSymbol>(
                declarator->name.valueText(), declarator->name.location(), direction);
            arg->setDeclaredType(*header.dataType);
            arg->setFromDeclarator(*declarator);
            arg->setAttributes(*result, syntax.attributes);

            result->addMember(*arg);
            arguments.append(arg);
        }
    }

    // The function gets an implicit variable inserted that represents the return value.
    if (subroutineKind == SubroutineKind::Function) {
        auto implicitReturnVar = compilation.emplace<VariableSymbol>(result->name, result->location,
                                                                     VariableLifetime::Automatic);
        implicitReturnVar->setDeclaredType(*proto->returnType);
        implicitReturnVar->isCompilerGenerated = true;
        result->addMember(*implicitReturnVar);
        result->returnValVar = implicitReturnVar;
        result->declaredReturnType.setTypeSyntax(*proto->returnType);
    }
    else {
        result->declaredReturnType.setType(compilation.getVoidType());
    }

    result->arguments = arguments.copy(compilation);
    result->binder.setItems(*result, syntax.items, syntax.sourceRange());
    return *result;
}

void SubroutineSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("returnType", getReturnType());
    serializer.write("defaultLifetime", toString(defaultLifetime));
    serializer.write("subroutineKind", toString(subroutineKind));
    serializer.write("body", getBody());

    serializer.startArray("arguments");
    for (auto const arg : arguments) {
        arg->serializeTo(serializer);
    }
    serializer.endArray();
}

ModportSymbol::ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Modport, name, loc), Scope(compilation, this) {
}

void ModportSymbol::fromSyntax(const Scope& parent, const ModportDeclarationSyntax& syntax,
                               SmallVector<const ModportSymbol*>& results) {
    auto& comp = parent.getCompilation();
    for (auto item : syntax.items) {
        // TODO: handle port list
        auto name = item->name;
        auto symbol = comp.emplace<ModportSymbol>(comp, name.valueText(), name.location());
        symbol->setSyntax(*item);
        symbol->setAttributes(parent, syntax.attributes);
        results.append(symbol);
    }
}

ContinuousAssignSymbol::ContinuousAssignSymbol(const ExpressionSyntax& syntax) :
    Symbol(SymbolKind::ContinuousAssign, "", syntax.getFirstToken().location()) {

    setSyntax(syntax);
}

ContinuousAssignSymbol::ContinuousAssignSymbol(SourceLocation loc, const Expression& assignment) :
    Symbol(SymbolKind::ContinuousAssign, "", loc), assign(&assignment) {
}

void ContinuousAssignSymbol::fromSyntax(Compilation& compilation,
                                        const ContinuousAssignSyntax& syntax, const Scope& scope,
                                        LookupLocation location,
                                        SmallVector<const Symbol*>& results) {
    BindContext context(scope, location);
    auto& netType = scope.getDefaultNetType();

    for (auto expr : syntax.assignments) {
        // If not explicitly disabled, check for net references on the lhs of each
        // assignment that should create implicit nets.
        if (!netType.isError()) {
            // The expression here should always be an assignment expression unless
            // the program is already ill-formed (diagnosed by the parser).
            if (expr->kind == SyntaxKind::AssignmentExpression) {
                SmallVectorSized<Token, 8> implicitNets;
                Expression::findPotentiallyImplicitNets(*expr->as<BinaryExpressionSyntax>().left,
                                                        context, implicitNets);

                for (Token t : implicitNets) {
                    auto net = compilation.emplace<NetSymbol>(t.valueText(), t.location(), netType);
                    net->setType(compilation.getLogicType());
                    results.append(net);
                }
            }
        }

        auto symbol = compilation.emplace<ContinuousAssignSymbol>(*expr);
        symbol->setAttributes(scope, syntax.attributes);
        results.append(symbol);
    }
}

const Expression& ContinuousAssignSymbol::getAssignment() const {
    if (assign)
        return *assign;

    auto scope = getParentScope();
    ASSERT(scope);

    auto syntax = getSyntax();
    ASSERT(syntax);

    BindContext context(*scope, LookupLocation::before(*this));
    assign =
        &Expression::bind(syntax->as<ExpressionSyntax>(), context, BindFlags::AssignmentAllowed);

    return *assign;
}

void ContinuousAssignSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("assignment", getAssignment());
}

GenvarSymbol::GenvarSymbol(string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Genvar, name, loc) {
}

void GenvarSymbol::fromSyntax(const Scope& parent, const GenvarDeclarationSyntax& syntax,
                              SmallVector<const GenvarSymbol*>& results) {
    auto& comp = parent.getCompilation();
    for (auto id : syntax.identifiers) {
        auto name = id->identifier;
        if (name.valueText().empty())
            continue;

        auto genvar = comp.emplace<GenvarSymbol>(name.valueText(), name.location());
        genvar->setSyntax(*id);
        genvar->setAttributes(parent, syntax.attributes);
        results.append(genvar);
    }
}

namespace {

GateSymbol* createGate(Compilation& compilation, const Scope& scope, GateType gateType,
                       const GateInstanceSyntax& syntax,
                       span<const AttributeInstanceSyntax* const> attributes) {
    string_view name;
    SourceLocation loc;
    if (syntax.decl) {
        name = syntax.decl->name.valueText();
        loc = syntax.decl->name.location();
    }
    else {
        name = "";
        loc = syntax.getFirstToken().location();
    }

    // TODO: ports!

    GateSymbol* gate = compilation.emplace<GateSymbol>(name, loc, gateType);
    gate->setSyntax(syntax);
    gate->setAttributes(scope, attributes);
    return gate;
};

using DimIterator = span<VariableDimensionSyntax*>::iterator;

Symbol* recurseGateArray(Compilation& compilation, GateType gateType,
                         const GateInstanceSyntax& instance, const BindContext& context,
                         DimIterator it, DimIterator end,
                         span<const AttributeInstanceSyntax* const> attributes) {
    if (it == end)
        return createGate(compilation, context.scope, gateType, instance, attributes);

    // Evaluate the dimensions of the array. If this fails for some reason,
    // make up an empty array so that we don't get further errors when
    // things try to reference this symbol.
    auto nameToken = instance.decl->name;
    EvaluatedDimension dim = context.evalDimension(**it, true);
    if (!dim.isRange()) {
        return compilation.emplace<GateArraySymbol>(compilation, nameToken.valueText(),
                                                    nameToken.location(),
                                                    span<const Symbol* const>{}, ConstantRange());
    }

    ++it;

    ConstantRange range = dim.range;
    SmallVectorSized<const Symbol*, 8> elements;
    for (int32_t i = range.lower(); i <= range.upper(); i++) {
        auto symbol =
            recurseGateArray(compilation, gateType, instance, context, it, end, attributes);
        symbol->name = "";
        elements.append(symbol);
    }

    auto result = compilation.emplace<GateArraySymbol>(compilation, nameToken.valueText(),
                                                       nameToken.location(),
                                                       elements.copy(compilation), range);
    for (auto element : elements)
        result->addMember(*element);

    return result;
}

} // namespace

void GateSymbol::fromSyntax(Compilation& compilation, const GateInstantiationSyntax& syntax,
                            LookupLocation location, const Scope& scope,
                            SmallVector<const Symbol*>& results) {
    // TODO: strengths and delays
    auto gateType = SemanticFacts::getGateType(syntax.gateType.kind);

    BindContext context(scope, location, BindFlags::Constant);
    for (auto instance : syntax.instances) {
        if (!instance->decl) {
            results.append(createGate(compilation, scope, gateType, *instance, syntax.attributes));
        }
        else {
            auto dims = instance->decl->dimensions;
            auto symbol = recurseGateArray(compilation, gateType, *instance, context, dims.begin(),
                                           dims.end(), syntax.attributes);
            results.append(symbol);
        }
    }
}

void GateSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("gateType", toString(gateType));
}

void GateArraySymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("range", range.toString());
}

} // namespace slang
