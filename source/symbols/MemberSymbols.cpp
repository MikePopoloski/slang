//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/MemberSymbols.h"

#include "slang/binding/Expression.h"
#include "slang/binding/FormatHelpers.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
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

SubroutineSymbol* SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const FunctionDeclarationSyntax& syntax,
                                               const Scope& parent, bool outOfBlock) {
    // If this subroutine has a scoped name, it should be an out of block declaration.
    // We shouldn't create a symbol now, since we need the class prototype to hook
    // us in to the correct scope. Register this syntax with the compilation so that
    // it can later be found by the prototype.
    auto proto = syntax.prototype;
    if (!outOfBlock && proto->name->kind == SyntaxKind::ScopedName) {
        // Remember the location in the parent scope where we *would* have inserted this
        // subroutine, for later use during lookup.
        uint32_t index = 1;
        if (auto last = parent.getLastMember())
            index = (uint32_t)last->getIndex() + 1;

        compilation.addOutOfBlockMethod(parent, syntax, SymbolIndex(index));
        return nullptr;
    }

    Token nameToken = proto->name->getLastToken();
    auto lifetime = SemanticFacts::getVariableLifetime(proto->lifetime);
    if (!lifetime.has_value()) {
        // Walk up to the nearest instance and use its default lifetime.
        // If we're not within an instance, default to static.
        lifetime = VariableLifetime::Static;
        auto scope = &parent;
        do {
            auto& sym = scope->asSymbol();
            if (sym.kind == SymbolKind::InstanceBody) {
                lifetime = sym.as<InstanceBodySymbol>().getDefinition().defaultLifetime;
                break;
            }
            else if (sym.kind == SymbolKind::ClassType) {
                lifetime = VariableLifetime::Automatic;
                break;
            }
            scope = sym.getParentScope();
        } while (scope);
    }

    auto subroutineKind = syntax.kind == SyntaxKind::TaskDeclaration ? SubroutineKind::Task
                                                                     : SubroutineKind::Function;
    auto result = compilation.emplace<SubroutineSymbol>(
        compilation, nameToken.valueText(), nameToken.location(), *lifetime, subroutineKind);

    result->setSyntax(syntax);
    result->setAttributes(parent, syntax.attributes);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto->portList)
        buildArguments(*result, *proto->portList, *lifetime, arguments);

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
                declarator->name.valueText(), declarator->name.location(), direction, *lifetime);
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
    return result;
}

SubroutineSymbol* SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const ClassMethodDeclarationSyntax& syntax,
                                               const Scope& parent) {
    auto result = fromSyntax(compilation, *syntax.declaration, parent, /* outOfBlock */ false);
    if (!result)
        return nullptr;

    result->setAttributes(parent, syntax.attributes);

    for (Token qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::LocalKeyword:
                result->visibility = Visibility::Local;
                break;
            case TokenKind::ProtectedKeyword:
                result->visibility = Visibility::Protected;
                break;
            case TokenKind::StaticKeyword:
                result->flags |= MethodFlags::Static;
                break;
            case TokenKind::PureKeyword:
                result->flags |= MethodFlags::Pure;
                break;
            case TokenKind::VirtualKeyword:
                result->flags |= MethodFlags::Virtual;
                break;
            case TokenKind::ConstKeyword:
            case TokenKind::ExternKeyword:
            case TokenKind::RandKeyword:
                // Parser already issued errors for these, so just ignore them here.
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    if (result->name == "new")
        result->flags |= MethodFlags::Constructor;

    return result;
}

SubroutineSymbol& SubroutineSymbol::createOutOfBlock(Compilation& compilation,
                                                     const FunctionDeclarationSyntax& syntax,
                                                     const ClassMethodPrototypeSymbol&,
                                                     const Scope& parent, SymbolIndex outOfBlockIndex) {
    auto result = fromSyntax(compilation, syntax, parent, /* outOfBlock */ true);
    ASSERT(result);

    // Set the parent pointer of the new subroutine so that lookups work correctly.
    // We won't actually exist in the scope's name map or be iterable through its members,
    // but nothing should be trying to look for these that way anyway.
    result->setParent(parent, SymbolIndex(INT32_MAX));
    result->outOfBlockIndex = outOfBlockIndex;

    // TODO: check / merge prototype

    return *result;
}

void SubroutineSymbol::buildArguments(Scope& scope, const FunctionPortListSyntax& syntax,
                                      VariableLifetime defaultLifetime,
                                      SmallVector<const FormalArgumentSymbol*>& arguments) {
    auto& comp = scope.getCompilation();
    const DataTypeSyntax* lastType = nullptr;
    auto lastDirection = ArgumentDirection::In;

    for (const FunctionPortSyntax* portSyntax : syntax.ports) {
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
        auto arg = comp.emplace<FormalArgumentSymbol>(
            declarator->name.valueText(), declarator->name.location(), direction, defaultLifetime);

        // If we're given a type, use that. Otherwise, if we were given a
        // direction, default to logic. Otherwise, use the last type.
        if (portSyntax->dataType) {
            arg->setDeclaredType(*portSyntax->dataType);
            lastType = portSyntax->dataType;
        }
        else if (directionSpecified || !lastType) {
            arg->setType(comp.getLogicType());
            lastType = nullptr;
        }
        else {
            arg->setDeclaredType(*lastType);
        }

        arg->setFromDeclarator(*declarator);
        arg->setAttributes(scope, portSyntax->attributes);

        scope.addMember(*arg);
        arguments.append(arg);
        lastDirection = direction;
    }
}

void SubroutineSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("returnType", getReturnType());
    serializer.write("defaultLifetime", toString(defaultLifetime));
    serializer.write("subroutineKind", toString(subroutineKind));
    serializer.write("body", getBody());
    serializer.write("visibility", toString(visibility));

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

    // TODO: handle drive strengths, delays
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
    auto dim = context.evalDimension(**it, /* requireRange */
                                     true, /* isPacked */ false);
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

ElabSystemTaskSymbol::ElabSystemTaskSymbol(ElabSystemTaskKind taskKind, SourceLocation loc) :
    Symbol(SymbolKind::ElabSystemTask, "", loc), taskKind(taskKind) {
}

ElabSystemTaskSymbol& ElabSystemTaskSymbol::fromSyntax(Compilation& compilation,
                                                       const ElabSystemTaskSyntax& syntax) {
    // Just create the symbol now. The diagnostic will be issued later
    // when someone visit the symbol and asks for it.
    auto taskKind = SemanticFacts::getElabSystemTaskKind(syntax.name);
    auto result = compilation.emplace<ElabSystemTaskSymbol>(taskKind, syntax.name.location());
    result->setSyntax(syntax);
    return *result;
}

string_view ElabSystemTaskSymbol::getMessage() const {
    if (message)
        return *message;

    auto syntax = getSyntax();
    ASSERT(syntax);

    auto empty = [&] {
        message = ""sv;
        return *message;
    };

    auto argSyntax = syntax->as<ElabSystemTaskSyntax>().arguments;
    if (!argSyntax)
        return empty();

    auto scope = getParentScope();
    ASSERT(scope);

    // Bind all arguments.
    auto& comp = scope->getCompilation();
    BindContext bindCtx(*scope, LookupLocation::before(*this), BindFlags::Constant);
    SmallVectorSized<const Expression*, 4> args;
    for (auto arg : argSyntax->parameters) {
        switch (arg->kind) {
            case SyntaxKind::OrderedArgument: {
                const auto& oa = arg->as<OrderedArgumentSyntax>();
                args.append(&Expression::bind(*oa.expr, bindCtx));
                break;
            }
            case SyntaxKind::NamedArgument:
                bindCtx.addDiag(diag::NamedArgNotAllowed, arg->sourceRange());
                return empty();
            case SyntaxKind::EmptyArgument:
                args.append(
                    comp.emplace<EmptyArgumentExpression>(comp.getVoidType(), arg->sourceRange()));
                break;
            default:
                THROW_UNREACHABLE;
        }

        if (args.back()->bad())
            return empty();
    }

    // If this is a $fatal task, check the finish number. We don't use this
    // for anything, but enforce that it's 0, 1, or 2.
    span<const Expression* const> argSpan = args;
    if (taskKind == ElabSystemTaskKind::Fatal && !argSpan.empty()) {
        if (!FmtHelpers::checkFinishNum(bindCtx, *argSpan[0]))
            return empty();

        argSpan = argSpan.subspan(1);
    }

    // Check all arguments.
    if (!FmtHelpers::checkDisplayArgs(bindCtx, argSpan))
        return empty();

    // Format the message to string.
    EvalContext evalCtx(comp);
    optional<std::string> str = FmtHelpers::formatDisplay(*scope, evalCtx, argSpan);
    if (!str)
        return empty();

    str->insert(0, ": ");

    // Copy the string into permanent memory.
    auto mem = comp.allocate(str->size(), alignof(char));
    memcpy(mem, str->data(), str->size());

    message = string_view(reinterpret_cast<char*>(mem), str->size());
    return *message;
}

void ElabSystemTaskSymbol::issueDiagnostic() const {
    auto scope = getParentScope();
    ASSERT(scope);

    DiagCode code;
    switch (taskKind) {
        case ElabSystemTaskKind::Fatal:
            code = diag::FatalTask;
            break;
        case ElabSystemTaskKind::Error:
            code = diag::ErrorTask;
            break;
        case ElabSystemTaskKind::Warning:
            code = diag::WarningTask;
            break;
        case ElabSystemTaskKind::Info:
            code = diag::InfoTask;
            break;
        default:
            THROW_UNREACHABLE;
    }

    scope->addDiag(code, location) << getMessage();
}

void ElabSystemTaskSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("taskKind", toString(taskKind));
    serializer.write("message", getMessage());
}

} // namespace slang
