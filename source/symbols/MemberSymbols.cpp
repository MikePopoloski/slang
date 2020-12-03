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
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/NetType.h"
#include "slang/types/Type.h"
#include "slang/util/StackContainer.h"

namespace slang {

EmptyMemberSymbol& EmptyMemberSymbol::fromSyntax(Compilation& compilation, const Scope& scope,
                                                 const EmptyMemberSyntax& syntax) {
    auto result = compilation.emplace<EmptyMemberSymbol>(syntax.semi.location());
    result->setAttributes(scope, syntax.attributes);

    // Report a warning if this is just an empty semicolon hanging out for no reason,
    // but don't report if this was inserted due to an error elsewhere.
    if (syntax.attributes.empty() && !syntax.semi.isMissing()) {
        // If there are skipped nodes behind this semicolon don't report the warning,
        // as it's likely it's due to the error itself.
        bool anySkipped = false;
        for (auto trivia : syntax.getFirstToken().trivia()) {
            if (trivia.kind == TriviaKind::SkippedTokens) {
                anySkipped = true;
                break;
            }
        }

        if (!anySkipped)
            scope.addDiag(diag::EmptyMember, syntax.sourceRange());
    }

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

ModportPortSymbol::ModportPortSymbol(string_view name, SourceLocation loc,
                                     ArgumentDirection direction) :
    ValueSymbol(SymbolKind::ModportPort, name, loc),
    direction(direction) {
}

ModportPortSymbol& ModportPortSymbol::fromSyntax(const Scope& parent, LookupLocation lookupLocation,
                                                 ArgumentDirection direction,
                                                 const ModportNamedPortSyntax& syntax) {
    auto& comp = parent.getCompilation();
    auto name = syntax.name;
    auto result = comp.emplace<ModportPortSymbol>(name.valueText(), name.location(), direction);
    result->setSyntax(syntax);
    result->internalSymbol = Lookup::unqualifiedAt(parent, name.valueText(), lookupLocation,
                                                   name.range(), LookupFlags::NoParentScope);

    if (result->internalSymbol) {
        if (result->internalSymbol->kind == SymbolKind::Subroutine) {
            auto& diag = parent.addDiag(diag::ExpectedImportExport, name.range());
            diag << name.valueText();
            diag.addNote(diag::NoteDeclarationHere, result->internalSymbol->location);
            result->internalSymbol = nullptr;
        }
        else if (!SemanticFacts::isAllowedInModport(result->internalSymbol->kind)) {
            auto& diag = parent.addDiag(diag::NotAllowedInModport, name.range());
            diag << name.valueText();
            diag.addNote(diag::NoteDeclarationHere, result->internalSymbol->location);
            result->internalSymbol = nullptr;
        }
    }

    if (result->internalSymbol) {
        auto sourceType = result->internalSymbol->getDeclaredType();
        ASSERT(sourceType);
        result->getDeclaredType()->copyTypeFrom(*sourceType);
    }

    return *result;
}

void ModportPortSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("direction", toString(direction));
    if (internalSymbol)
        serializer.writeLink("internalSymbol", *internalSymbol);
}

ModportSymbol::ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Modport, name, loc), Scope(compilation, this) {
}

void ModportSymbol::fromSyntax(const Scope& parent, const ModportDeclarationSyntax& syntax,
                               LookupLocation lookupLocation,
                               SmallVector<const ModportSymbol*>& results) {
    auto& comp = parent.getCompilation();
    for (auto item : syntax.items) {
        auto modport =
            comp.emplace<ModportSymbol>(comp, item->name.valueText(), item->name.location());
        modport->setSyntax(*item);
        modport->setAttributes(parent, syntax.attributes);
        results.append(modport);

        for (auto port : item->ports->ports) {
            switch (port->kind) {
                case SyntaxKind::ModportSimplePortList: {
                    auto& portList = port->as<ModportSimplePortListSyntax>();
                    auto direction = SemanticFacts::getDirection(portList.direction.kind);
                    for (auto simplePort : portList.ports) {
                        switch (simplePort->kind) {
                            case SyntaxKind::ModportNamedPort: {
                                auto& mpp = ModportPortSymbol::fromSyntax(
                                    parent, lookupLocation, direction,
                                    simplePort->as<ModportNamedPortSyntax>());
                                mpp.setAttributes(*modport, portList.attributes);
                                modport->addMember(mpp);
                                break;
                            }
                            case SyntaxKind::ModportExplicitPort:
                                parent.addDiag(diag::NotYetSupported, simplePort->sourceRange());
                                break;
                            default:
                                THROW_UNREACHABLE;
                        }
                    }
                    break;
                }
                case SyntaxKind::ModportSubroutinePortList: {
                    auto& portList = port->as<ModportSubroutinePortListSyntax>();
                    if (portList.importExport.kind == TokenKind::ExportKeyword) {
                        // TODO: implement
                    }
                    else {
                        for (auto subPort : portList.ports) {
                            switch (subPort->kind) {
                                case SyntaxKind::ModportNamedPort: {
                                    auto& mps = MethodPrototypeSymbol::fromSyntax(
                                        parent, lookupLocation,
                                        subPort->as<ModportNamedPortSyntax>());
                                    mps.setAttributes(*modport, portList.attributes);
                                    modport->addMember(mps);
                                    break;
                                }
                                case SyntaxKind::ModportSubroutinePort: {
                                    auto& mps = MethodPrototypeSymbol::fromSyntax(
                                        parent, subPort->as<ModportSubroutinePortSyntax>());
                                    mps.setAttributes(*modport, portList.attributes);
                                    modport->addMember(mps);
                                    break;
                                }
                                default:
                                    THROW_UNREACHABLE;
                            }
                        }
                    }
                    break;
                }
                case SyntaxKind::ModportClockingPort:
                    parent.addDiag(diag::NotYetSupported, port->sourceRange());
                    break;
                default:
                    THROW_UNREACHABLE;
            }
        }
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
