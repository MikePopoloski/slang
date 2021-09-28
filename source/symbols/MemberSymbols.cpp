//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/MemberSymbols.h"

#include "slang/binding/AssertionExpr.h"
#include "slang/binding/AssignmentExpressions.h"
#include "slang/binding/Expression.h"
#include "slang/binding/FormatHelpers.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ASTVisitor.h"
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

static const PackageSymbol* findPackage(string_view packageName, const Scope& lookupScope,
                                        SourceLocation errorLoc) {
    auto package = lookupScope.getCompilation().getPackage(packageName);
    if (!package && !packageName.empty())
        lookupScope.addDiag(diag::UnknownPackage, errorLoc) << packageName;
    return package;
}

const Symbol* ExplicitImportSymbol::importedSymbol() const {
    if (!initialized) {
        initialized = true;

        const Scope* scope = getParentScope();
        ASSERT(scope);

        auto loc = location;
        if (auto syntax = getSyntax())
            loc = syntax->as<PackageImportItemSyntax>().package.location();

        package_ = findPackage(packageName, *scope, loc);
        if (!package_)
            return nullptr;

        import = package_->findForImport(importName);
        if (!import) {
            if (!importName.empty()) {
                loc = location;
                if (auto syntax = getSyntax())
                    loc = syntax->as<PackageImportItemSyntax>().item.location();

                auto& diag = scope->addDiag(diag::UnknownPackageMember, loc);
                diag << importName << name;
            }
        }
        else {
            // If we are doing this lookup from a scope that is within a package declaration
            // we should note that fact so that it can later be exported if desired.
            do {
                auto& sym = scope->asSymbol();
                if (sym.kind == SymbolKind::Package) {
                    sym.as<PackageSymbol>().noteImport(*import);
                    break;
                }

                scope = sym.getParentScope();
            } while (scope);
        }
    }
    return import;
}

void ExplicitImportSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("isFromExport", isFromExport);
    if (auto pkg = package())
        serializer.writeLink("package", *pkg);

    if (auto sym = importedSymbol())
        serializer.writeLink("import", *sym);
}

void WildcardImportSymbol::setPackage(const PackageSymbol& pkg) {
    package = &pkg;
}

const PackageSymbol* WildcardImportSymbol::getPackage() const {
    if (!package) {
        const Scope* scope = getParentScope();
        ASSERT(scope);

        auto loc = location;
        if (auto syntax = getSyntax(); syntax)
            loc = syntax->as<PackageImportItemSyntax>().package.location();

        package = findPackage(packageName, *scope, loc);
    }
    return *package;
}

void WildcardImportSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("isFromExport", isFromExport);
    if (auto pkg = getPackage())
        serializer.writeLink("package", *pkg);
}

ModportPortSymbol::ModportPortSymbol(string_view name, SourceLocation loc,
                                     ArgumentDirection direction) :
    ValueSymbol(SymbolKind::ModportPort, name, loc),
    direction(direction) {
}

ModportPortSymbol& ModportPortSymbol::fromSyntax(const BindContext& context,
                                                 ArgumentDirection direction,
                                                 const ModportNamedPortSyntax& syntax) {
    auto& comp = context.getCompilation();
    auto name = syntax.name;
    auto result = comp.emplace<ModportPortSymbol>(name.valueText(), name.location(), direction);
    result->setSyntax(syntax);
    result->internalSymbol =
        Lookup::unqualifiedAt(*context.scope, name.valueText(), context.getLocation(), name.range(),
                              LookupFlags::NoParentScope);

    if (result->internalSymbol) {
        if (result->internalSymbol->kind == SymbolKind::Subroutine) {
            auto& diag = context.addDiag(diag::ExpectedImportExport, name.range());
            diag << name.valueText();
            diag.addNote(diag::NoteDeclarationHere, result->internalSymbol->location);
            result->internalSymbol = nullptr;
        }
        else if (!SemanticFacts::isAllowedInModport(result->internalSymbol->kind)) {
            auto& diag = context.addDiag(diag::NotAllowedInModport, name.range());
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

ModportClockingSymbol::ModportClockingSymbol(string_view name, SourceLocation loc) :
    Symbol(SymbolKind::ModportClocking, name, loc) {
}

ModportClockingSymbol& ModportClockingSymbol::fromSyntax(const BindContext& context,
                                                         const ModportClockingPortSyntax& syntax) {
    auto& comp = context.getCompilation();
    auto name = syntax.name;
    auto result = comp.emplace<ModportClockingSymbol>(name.valueText(), name.location());
    result->setSyntax(syntax);

    result->target = Lookup::unqualifiedAt(*context.scope, name.valueText(), context.getLocation(),
                                           name.range(), LookupFlags::NoParentScope);

    if (result->target && result->target->kind != SymbolKind::ClockingBlock) {
        auto& diag = context.addDiag(diag::NotAClockingBlock, name.range());
        diag << name.valueText();
        diag.addNote(diag::NoteDeclarationHere, result->target->location);
        result->target = nullptr;
    }

    return *result;
}

void ModportClockingSymbol::serializeTo(ASTSerializer& serializer) const {
    if (target)
        serializer.writeLink("target", *target);
}

ModportSymbol::ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Modport, name, loc), Scope(compilation, this) {
}

void ModportSymbol::fromSyntax(const BindContext& context, const ModportDeclarationSyntax& syntax,
                               SmallVector<const ModportSymbol*>& results) {
    auto& comp = context.getCompilation();
    for (auto item : syntax.items) {
        auto modport =
            comp.emplace<ModportSymbol>(comp, item->name.valueText(), item->name.location());
        modport->setSyntax(*item);
        modport->setAttributes(*context.scope, syntax.attributes);
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
                                    context, direction, simplePort->as<ModportNamedPortSyntax>());
                                mpp.setAttributes(*modport, portList.attributes);
                                modport->addMember(mpp);
                                break;
                            }
                            case SyntaxKind::ModportExplicitPort:
                                context.addDiag(diag::NotYetSupported, simplePort->sourceRange());
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
                                        context, subPort->as<ModportNamedPortSyntax>());
                                    mps.setAttributes(*modport, portList.attributes);
                                    modport->addMember(mps);
                                    break;
                                }
                                case SyntaxKind::ModportSubroutinePort: {
                                    auto& mps = MethodPrototypeSymbol::fromSyntax(
                                        *context.scope, subPort->as<ModportSubroutinePortSyntax>());
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
                case SyntaxKind::ModportClockingPort: {
                    auto& clockingPort = port->as<ModportClockingPortSyntax>();
                    auto& mcs = ModportClockingSymbol::fromSyntax(context, clockingPort);
                    mcs.setAttributes(*modport, clockingPort.attributes);
                    modport->addMember(mcs);
                    break;
                }
                default: {
                    THROW_UNREACHABLE;
                }
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
                                        const ContinuousAssignSyntax& syntax,
                                        const BindContext& parentContext,
                                        SmallVector<const Symbol*>& results,
                                        SmallVector<const Symbol*>& implicitNets) {
    BindContext context = parentContext.resetFlags(BindFlags::NonProcedural);
    auto& netType = context.scope->getDefaultNetType();

    for (auto expr : syntax.assignments) {
        // If not explicitly disabled, check for net references on the lhs of each
        // assignment that should create implicit nets.
        if (!netType.isError()) {
            // The expression here should always be an assignment expression unless
            // the program is already ill-formed (diagnosed by the parser).
            if (expr->kind == SyntaxKind::AssignmentExpression) {
                SmallVectorSized<Token, 8> implicitNetNames;
                Expression::findPotentiallyImplicitNets(*expr->as<BinaryExpressionSyntax>().left,
                                                        context, implicitNetNames);

                for (Token t : implicitNetNames) {
                    auto net = compilation.emplace<NetSymbol>(t.valueText(), t.location(), netType);
                    net->setType(compilation.getLogicType());
                    implicitNets.append(net);
                }
            }
        }

        auto symbol = compilation.emplace<ContinuousAssignSymbol>(*expr);
        symbol->setAttributes(*context.scope, syntax.attributes);
        results.append(symbol);
    }
}

const Expression& ContinuousAssignSymbol::getAssignment() const {
    if (assign)
        return *assign;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    ASSERT(scope && syntax);

    BindContext context(*scope, LookupLocation::after(*this), BindFlags::NonProcedural);
    assign =
        &Expression::bind(syntax->as<ExpressionSyntax>(), context, BindFlags::AssignmentAllowed);

    return *assign;
}

struct ExpressionVarVisitor {
    bool anyVars = false;

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            switch (expr.kind) {
                case ExpressionKind::NamedValue:
                case ExpressionKind::HierarchicalValue: {
                    if (auto sym = expr.getSymbolReference()) {
                        if (VariableSymbol::isKind(sym->kind))
                            anyVars = true;
                    }
                    break;
                }
                default:
                    if constexpr (is_detected_v<ASTDetectors::visitExprs_t, T,
                                                ExpressionVarVisitor>) {
                        expr.visitExprs(*this);
                    }
                    break;
            }
        }
    }

    void visitInvalid(const Expression&) {}
    void visitInvalid(const AssertionExpr&) {}
};

const TimingControl* ContinuousAssignSymbol::getDelay() const {
    if (delay)
        return *delay;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    if (!scope || !syntax || !syntax->parent) {
        delay = nullptr;
        return nullptr;
    }

    auto delaySyntax = syntax->parent->as<ContinuousAssignSyntax>().delay;
    if (!delaySyntax) {
        delay = nullptr;
        return nullptr;
    }

    BindContext context(*scope, LookupLocation::before(*this), BindFlags::NonProcedural);
    delay = &TimingControl::bind(*delaySyntax, context);

    // A multi-delay is disallowed if the lhs references variables.
    auto& d = *delay.value();
    if (d.kind == TimingControlKind::Delay3) {
        auto& d3 = d.as<Delay3Control>();
        if (d3.expr2) {
            auto& expr = getAssignment();
            if (expr.kind == ExpressionKind::Assignment) {
                auto& left = expr.as<AssignmentExpression>().left();
                ExpressionVarVisitor visitor;
                left.visit(visitor);
                if (visitor.anyVars)
                    context.addDiag(diag::Delay3OnVar, left.sourceRange);
            }
        }
    }

    return *delay;
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

ElabSystemTaskSymbol::ElabSystemTaskSymbol(ElabSystemTaskKind taskKind, SourceLocation loc) :
    Symbol(SymbolKind::ElabSystemTask, "", loc), taskKind(taskKind) {
}

ElabSystemTaskSymbol& ElabSystemTaskSymbol::fromSyntax(Compilation& compilation,
                                                       const ElabSystemTaskSyntax& syntax) {
    // Just create the symbol now. The diagnostic will be issued later
    // when someone visits the symbol and asks for it.
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
                if (auto exSyn = bindCtx.requireSimpleExpr(*oa.expr))
                    args.append(&Expression::bind(*exSyn, bindCtx));
                else
                    return empty();
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
    evalCtx.reportDiags(bindCtx);

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

PrimitivePortSymbol::PrimitivePortSymbol(Compilation& compilation, string_view name,
                                         SourceLocation loc, PrimitivePortDirection direction) :
    ValueSymbol(SymbolKind::PrimitivePort, name, loc),
    direction(direction) {
    // All primitive ports are single bit logic types.
    setType(compilation.getLogicType());
}

void PrimitivePortSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("direction", toString(direction));
}

PrimitiveSymbol& PrimitiveSymbol::fromSyntax(const Scope& scope,
                                             const UdpDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto prim = comp.emplace<PrimitiveSymbol>(comp, syntax.name.valueText(), syntax.name.location(),
                                              PrimitiveSymbol::UserDefined);
    prim->setAttributes(scope, syntax.attributes);
    prim->setSyntax(syntax);

    SmallVectorSized<const PrimitivePortSymbol*, 4> ports;
    if (syntax.portList->kind == SyntaxKind::AnsiUdpPortList) {
        for (auto decl : syntax.portList->as<AnsiUdpPortListSyntax>().ports) {
            if (decl->kind == SyntaxKind::UdpOutputPortDecl) {
                auto& outputDecl = decl->as<UdpOutputPortDeclSyntax>();
                PrimitivePortDirection dir = PrimitivePortDirection::Out;
                if (outputDecl.reg)
                    dir = PrimitivePortDirection::OutReg;

                auto port = comp.emplace<PrimitivePortSymbol>(comp, outputDecl.name.valueText(),
                                                              outputDecl.name.location(), dir);
                port->setSyntax(*decl);
                port->setAttributes(scope, decl->attributes);
                ports.append(port);
                prim->addMember(*port);
            }
            else {
                auto& inputDecl = decl->as<UdpInputPortDeclSyntax>();
                for (auto nameSyntax : inputDecl.names) {
                    auto name = nameSyntax->identifier;
                    auto port = comp.emplace<PrimitivePortSymbol>(
                        comp, name.valueText(), name.location(), PrimitivePortDirection::In);

                    port->setSyntax(*nameSyntax);
                    port->setAttributes(scope, decl->attributes);
                    ports.append(port);
                    prim->addMember(*port);
                }
            }
        }

        if (!syntax.body->portDecls.empty())
            scope.addDiag(diag::PrimitiveAnsiMix, syntax.body->portDecls[0]->sourceRange());
    }
    else if (syntax.portList->kind == SyntaxKind::NonAnsiUdpPortList) {
        // In the non-ansi case the port list only gives the ordering, we need to
        // look through the body decls to get the rest of the port info.
        SmallMap<string_view, PrimitivePortSymbol*, 4> portMap;
        for (auto nameSyntax : syntax.portList->as<NonAnsiUdpPortListSyntax>().ports) {
            auto name = nameSyntax->identifier;
            auto port = comp.emplace<PrimitivePortSymbol>(comp, name.valueText(), name.location(),
                                                          PrimitivePortDirection::In);
            ports.append(port);
            prim->addMember(*port);
            if (!name.valueText().empty())
                portMap.emplace(name.valueText(), port);
        }

        auto checkDup = [&](auto port, auto nameToken) {
            // If this port already has a syntax node set it's a duplicate declaration.
            if (auto prevSyntax = port->getSyntax()) {
                auto& diag = scope.addDiag(diag::PrimitivePortDup, nameToken.range());
                diag << nameToken.valueText();
                diag.addNote(diag::NotePreviousDefinition, port->location);
            }
        };

        const UdpOutputPortDeclSyntax* regSpecifier = nullptr;
        for (auto decl : syntax.body->portDecls) {
            if (decl->kind == SyntaxKind::UdpOutputPortDecl) {
                auto& outputDecl = decl->as<UdpOutputPortDeclSyntax>();
                if (auto it = portMap.find(outputDecl.name.valueText()); it != portMap.end()) {
                    // Standalone "reg" specifiers should be saved and processed at the
                    // end once we've handled all of the regular declarations.
                    if (outputDecl.reg && !outputDecl.keyword) {
                        if (regSpecifier) {
                            auto& diag =
                                scope.addDiag(diag::PrimitiveRegDup, outputDecl.reg.range());
                            diag.addNote(diag::NotePreviousDefinition,
                                         regSpecifier->reg.location());
                        }
                        regSpecifier = &outputDecl;
                        continue;
                    }

                    auto port = it->second;
                    checkDup(port, outputDecl.name);

                    port->direction = PrimitivePortDirection::Out;
                    if (outputDecl.reg)
                        port->direction = PrimitivePortDirection::OutReg;

                    port->location = outputDecl.name.location();
                    port->setSyntax(outputDecl);
                    port->setAttributes(scope, decl->attributes);
                }
                else {
                    auto& diag = scope.addDiag(diag::PrimitivePortUnknown, outputDecl.name.range());
                    diag << outputDecl.name.valueText();
                }
            }
            else {
                auto& inputDecl = decl->as<UdpInputPortDeclSyntax>();
                for (auto nameSyntax : inputDecl.names) {
                    auto name = nameSyntax->identifier;
                    if (auto it = portMap.find(name.valueText()); it != portMap.end()) {
                        auto port = it->second;
                        checkDup(port, name);

                        // Direction is already set to In here, so just update
                        // our syntax, location, etc.
                        port->location = name.location();
                        port->setSyntax(*nameSyntax);
                        port->setAttributes(scope, decl->attributes);
                    }
                    else {
                        auto& diag = scope.addDiag(diag::PrimitivePortUnknown, name.range());
                        diag << name.valueText();
                    }
                }
            }
        }

        if (regSpecifier) {
            auto name = regSpecifier->name;
            auto it = portMap.find(name.valueText());
            ASSERT(it != portMap.end());

            auto port = it->second;
            if (port->getSyntax()) {
                if (port->direction == PrimitivePortDirection::OutReg) {
                    checkDup(port, name);
                }
                else if (port->direction == PrimitivePortDirection::In) {
                    auto& diag = scope.addDiag(diag::PrimitiveRegInput, name.range());
                    diag << port->name;
                }
                else {
                    port->direction = PrimitivePortDirection::OutReg;
                }
            }
        }

        for (auto port : ports) {
            if (!port->getSyntax()) {
                auto& diag = scope.addDiag(diag::PrimitivePortMissing, port->location);
                diag << port->name;
            }
        }
    }
    else if (syntax.portList->kind == SyntaxKind::WildcardUdpPortList) {
        // TODO:
    }
    else {
        THROW_UNREACHABLE;
    }

    if (ports.size() < 2)
        scope.addDiag(diag::PrimitiveTwoPorts, prim->location);
    else if (ports[0]->direction == PrimitivePortDirection::In)
        scope.addDiag(diag::PrimitiveOutputFirst, ports[0]->location);
    else {
        const ExpressionSyntax* initExpr = nullptr;
        if (ports[0]->direction == PrimitivePortDirection::OutReg) {
            prim->isSequential = true;

            // If the first port is an 'output reg' check if it specifies
            // the initial value inline.
            auto portSyntax = ports[0]->getSyntax();
            if (portSyntax && portSyntax->kind == SyntaxKind::UdpOutputPortDecl) {
                auto& outSyntax = portSyntax->as<UdpOutputPortDeclSyntax>();
                if (outSyntax.initializer)
                    initExpr = outSyntax.initializer->expr;
            }
        }

        // Make sure we have only one output port.
        for (size_t i = 1; i < ports.size(); i++) {
            if (ports[i]->direction != PrimitivePortDirection::In) {
                scope.addDiag(diag::PrimitiveDupOutput, ports[i]->location);
                break;
            }
        }

        // If we have an initial statement check it for correctness.
        if (auto initial = syntax.body->initialStmt) {
            if (!prim->isSequential)
                scope.addDiag(diag::PrimitiveInitialInComb, initial->sourceRange());
            else if (initExpr) {
                auto& diag = scope.addDiag(diag::PrimitiveDupInitial, initial->sourceRange());
                diag.addNote(diag::NotePreviousDefinition, initExpr->getFirstToken().location());
            }
            else {
                initExpr = initial->value;

                auto initialName = initial->name.valueText();
                if (!initialName.empty() && !ports[0]->name.empty() &&
                    initialName != ports[0]->name) {
                    auto& diag = scope.addDiag(diag::PrimitiveWrongInitial, initial->name.range());
                    diag << initialName;
                    diag.addNote(diag::NoteDeclarationHere, ports[0]->location);
                }
            }
        }

        if (initExpr) {
            BindContext context(scope, LookupLocation::max);
            auto& expr = Expression::bind(*initExpr, context, BindFlags::Constant);
            if (!expr.bad()) {
                if (expr.kind == ExpressionKind::IntegerLiteral &&
                    (expr.type->getBitWidth() == 1 || expr.isUnsizedInteger())) {
                    context.eval(expr);
                    if (expr.constant) {
                        auto& val = expr.constant->integer();
                        if (val == 0 || val == 1 ||
                            (val.getBitWidth() == 1 && exactlyEqual(val[0], logic_t::x))) {
                            prim->initVal = expr.constant;
                        }
                    }
                }

                if (!prim->initVal)
                    scope.addDiag(diag::PrimitiveInitVal, expr.sourceRange);
            }
        }
    }

    // TODO: body

    prim->ports = ports.copy(comp);
    return *prim;
}

void PrimitiveSymbol::serializeTo(ASTSerializer&) const {
    // TODO:
}

SpecifyBlockSymbol::SpecifyBlockSymbol(Compilation& compilation, SourceLocation loc) :
    Symbol(SymbolKind::SpecifyBlock, "", loc), Scope(compilation, this) {
}

SpecifyBlockSymbol& SpecifyBlockSymbol::fromSyntax(Scope& scope, const SpecifyBlockSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<SpecifyBlockSymbol>(comp, syntax.specify.location());
    result->setSyntax(syntax);

    for (auto member : syntax.items)
        result->addMembers(*member);

    // specparams inside specify blocks get visibility in the parent scope as well.
    for (auto member = result->getFirstMember(); member; member = member->getNextSibling()) {
        if (member->kind == SymbolKind::Specparam)
            scope.addMember(*comp.emplace<TransparentMemberSymbol>(*member));
    }

    return *result;
}

AssertionPortSymbol::AssertionPortSymbol(string_view name, SourceLocation loc) :
    Symbol(SymbolKind::AssertionPort, name, loc), declaredType(*this) {
}

void AssertionPortSymbol::buildPorts(Scope& scope, const AssertionItemPortListSyntax& syntax,
                                     SmallVector<const AssertionPortSymbol*>& results) {
    auto isEmpty = [](const DataTypeSyntax& syntax) {
        if (syntax.kind != SyntaxKind::ImplicitType)
            return false;

        auto& implicit = syntax.as<ImplicitTypeSyntax>();
        return !implicit.signing && implicit.dimensions.empty();
    };

    auto& comp = scope.getCompilation();
    auto& untyped = comp.getType(SyntaxKind::Untyped);
    const DataTypeSyntax* lastType = nullptr;
    optional<ArgumentDirection> lastLocalDir;

    for (auto item : syntax.ports) {
        auto port =
            comp.emplace<AssertionPortSymbol>(item->name.valueText(), item->name.location());
        port->setSyntax(*item);
        port->setAttributes(scope, item->attributes);

        if (!item->dimensions.empty())
            port->declaredType.setDimensionSyntax(item->dimensions);

        if (item->local) {
            port->localVarDirection = item->direction
                                          ? SemanticFacts::getDirection(item->direction.kind)
                                          : ArgumentDirection::In;

            // If we have a local keyword we can never inherit the previous type.
            lastType = nullptr;

            if (scope.asSymbol().kind == SymbolKind::Property &&
                port->localVarDirection != ArgumentDirection::In) {
                scope.addDiag(diag::AssertionPortPropOutput, item->direction.range());
            }
        }

        if (isEmpty(*item->type)) {
            if (lastType)
                port->declaredType.setTypeSyntax(*lastType);
            else {
                port->declaredType.setType(untyped);
                if (!item->dimensions.empty()) {
                    scope.addDiag(diag::InvalidArrayElemType, item->dimensions.sourceRange())
                        << untyped;
                }

                if (item->local && scope.asSymbol().kind != SymbolKind::LetDecl)
                    scope.addDiag(diag::LocalVarTypeRequired, item->local.range());
            }

            if (!item->local)
                port->localVarDirection = lastLocalDir;
        }
        else {
            port->declaredType.setTypeSyntax(*item->type);
            lastType = item->type;

            // Ports of type 'property' are not allowed in sequences,
            // and let declarations cannot have ports of type 'sequence' or 'property'.
            auto itemKind = item->type->kind;
            if (itemKind == SyntaxKind::PropertyType &&
                scope.asSymbol().kind == SymbolKind::Sequence) {
                scope.addDiag(diag::PropertyPortInSeq, item->type->sourceRange());
            }
            else if ((itemKind == SyntaxKind::PropertyType ||
                      itemKind == SyntaxKind::SequenceType) &&
                     scope.asSymbol().kind == SymbolKind::LetDecl) {
                scope.addDiag(diag::PropertyPortInLet, item->type->sourceRange())
                    << item->type->getFirstToken().valueText();
            }
        }

        lastLocalDir = port->localVarDirection;
        if (item->defaultValue) {
            if (port->localVarDirection == ArgumentDirection::Out ||
                port->localVarDirection == ArgumentDirection::InOut) {
                scope.addDiag(diag::AssertionPortOutputDefault,
                              item->defaultValue->expr->sourceRange());
            }
            else {
                port->defaultValueSyntax = item->defaultValue->expr;
            }
        }

        if (port->localVarDirection) {
            port->declaredType.addFlags(DeclaredTypeFlags::RequireSequenceType);
        }

        scope.addMember(*port);
        results.append(port);
    }
}

void AssertionPortSymbol::serializeTo(ASTSerializer& serializer) const {
    if (localVarDirection)
        serializer.write("localVarDirection", toString(*localVarDirection));
}

SequenceSymbol::SequenceSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Sequence, name, loc), Scope(compilation, this) {
}

SequenceSymbol& SequenceSymbol::fromSyntax(const Scope& scope,
                                           const SequenceDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result =
        comp.emplace<SequenceSymbol>(comp, syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);

    SmallVectorSized<const AssertionPortSymbol*, 4> ports;
    if (syntax.portList)
        AssertionPortSymbol::buildPorts(*result, *syntax.portList, ports);
    result->ports = ports.copy(comp);

    return *result;
}

void SequenceSymbol::makeDefaultInstance() const {
    AssertionInstanceExpression::makeDefault(*this);
}

PropertySymbol::PropertySymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Property, name, loc), Scope(compilation, this) {
}

PropertySymbol& PropertySymbol::fromSyntax(const Scope& scope,
                                           const PropertyDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result =
        comp.emplace<PropertySymbol>(comp, syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);

    SmallVectorSized<const AssertionPortSymbol*, 4> ports;
    if (syntax.portList)
        AssertionPortSymbol::buildPorts(*result, *syntax.portList, ports);
    result->ports = ports.copy(comp);

    return *result;
}

void PropertySymbol::makeDefaultInstance() const {
    AssertionInstanceExpression::makeDefault(*this);
}

LetDeclSymbol::LetDeclSymbol(Compilation& compilation, const ExpressionSyntax& exprSyntax,
                             string_view name, SourceLocation loc) :
    Symbol(SymbolKind::LetDecl, name, loc),
    Scope(compilation, this), exprSyntax(&exprSyntax) {
}

LetDeclSymbol& LetDeclSymbol::fromSyntax(const Scope& scope, const LetDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<LetDeclSymbol>(comp, *syntax.expr, syntax.identifier.valueText(),
                                              syntax.identifier.location());
    result->setSyntax(syntax);

    SmallVectorSized<const AssertionPortSymbol*, 4> ports;
    if (syntax.portList)
        AssertionPortSymbol::buildPorts(*result, *syntax.portList, ports);
    result->ports = ports.copy(comp);

    return *result;
}

void LetDeclSymbol::makeDefaultInstance() const {
    AssertionInstanceExpression::makeDefault(*this);
}

ClockingBlockSymbol::ClockingBlockSymbol(Compilation& compilation, string_view name,
                                         SourceLocation loc) :
    Symbol(SymbolKind::ClockingBlock, name, loc),
    Scope(compilation, this) {
}

ClockingBlockSymbol& ClockingBlockSymbol::fromSyntax(const Scope& scope,
                                                     const ClockingDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ClockingBlockSymbol>(comp, syntax.blockName.valueText(),
                                                    syntax.blockName.location());
    result->setSyntax(syntax);

    if (syntax.globalOrDefault.kind == TokenKind::DefaultKeyword)
        comp.noteDefaultClocking(scope, *result, syntax.clocking.range());
    else if (syntax.globalOrDefault.kind == TokenKind::GlobalKeyword) {
        comp.noteGlobalClocking(scope, *result, syntax.clocking.range());
        if (scope.asSymbol().kind == SymbolKind::GenerateBlock)
            scope.addDiag(diag::GlobalClockingGenerate, syntax.clocking.range());
    }

    const ClockingSkewSyntax* inputSkew = nullptr;
    const ClockingSkewSyntax* outputSkew = nullptr;

    for (auto item : syntax.items) {
        if (item->kind == SyntaxKind::DefaultSkewItem) {
            auto& dir = *item->as<DefaultSkewItemSyntax>().direction;
            if (dir.inputSkew) {
                if (inputSkew) {
                    auto& diag =
                        scope.addDiag(diag::MultipleDefaultInputSkew, dir.inputSkew->sourceRange());
                    diag.addNote(diag::NotePreviousDefinition,
                                 inputSkew->getFirstToken().location());
                }
                else {
                    inputSkew = dir.inputSkew;
                }
            }

            if (dir.outputSkew) {
                if (outputSkew) {
                    auto& diag = scope.addDiag(diag::MultipleDefaultOutputSkew,
                                               dir.outputSkew->sourceRange());
                    diag.addNote(diag::NotePreviousDefinition,
                                 outputSkew->getFirstToken().location());
                }
                else {
                    outputSkew = dir.outputSkew;
                }
            }
        }
        else {
            result->addMembers(*item);
        }
    }

    result->inputSkewSyntax = inputSkew;
    result->outputSkewSyntax = outputSkew;

    return *result;
}

const TimingControl& ClockingBlockSymbol::getEvent() const {
    if (!event) {
        auto scope = getParentScope();
        auto syntax = getSyntax();
        ASSERT(scope && syntax);

        BindContext context(*scope, LookupLocation::before(*this));
        event = &EventListControl::fromSyntax(
            getCompilation(), *syntax->as<ClockingDeclarationSyntax>().event, context);
    }
    return *event;
}

ClockingSkew ClockingBlockSymbol::getDefaultInputSkew() const {
    if (!defaultInputSkew) {
        if (inputSkewSyntax) {
            auto scope = getParentScope();
            ASSERT(scope);

            BindContext context(*scope, LookupLocation::before(*this));
            defaultInputSkew = ClockingSkew::fromSyntax(*inputSkewSyntax, context);
        }
        else {
            defaultInputSkew.emplace();
        }
    }
    return *defaultInputSkew;
}

ClockingSkew ClockingBlockSymbol::getDefaultOutputSkew() const {
    if (!defaultOutputSkew) {
        if (outputSkewSyntax) {
            auto scope = getParentScope();
            ASSERT(scope);

            BindContext context(*scope, LookupLocation::before(*this));
            defaultOutputSkew = ClockingSkew::fromSyntax(*outputSkewSyntax, context);
        }
        else {
            defaultOutputSkew.emplace();
        }
    }
    return *defaultOutputSkew;
}

void ClockingBlockSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("event", getEvent());

    if (auto skew = getDefaultInputSkew(); skew.hasValue()) {
        serializer.writeProperty("defaultInputSkew");
        serializer.startObject();
        skew.serializeTo(serializer);
        serializer.endObject();
    }

    if (auto skew = getDefaultOutputSkew(); skew.hasValue()) {
        serializer.writeProperty("defaultOutputSkew");
        serializer.startObject();
        skew.serializeTo(serializer);
        serializer.endObject();
    }
}

RandSeqProductionSymbol::RandSeqProductionSymbol(Compilation& compilation, string_view name,
                                                 SourceLocation loc) :
    Symbol(SymbolKind::RandSeqProduction, name, loc),
    Scope(compilation, this), declaredReturnType(*this) {
}

RandSeqProductionSymbol& RandSeqProductionSymbol::fromSyntax(Compilation& compilation,
                                                             const ProductionSyntax& syntax) {
    auto result = compilation.emplace<RandSeqProductionSymbol>(compilation, syntax.name.valueText(),
                                                               syntax.name.location());
    result->setSyntax(syntax);

    if (syntax.dataType)
        result->declaredReturnType.setTypeSyntax(*syntax.dataType);
    else
        result->declaredReturnType.setType(compilation.getVoidType());

    if (syntax.portList) {
        SmallVectorSized<const FormalArgumentSymbol*, 8> args;
        SubroutineSymbol::buildArguments(*result, *syntax.portList, VariableLifetime::Automatic,
                                         args);
        result->arguments = args.copy(compilation);
    }

    for (auto rule : syntax.rules) {
        auto& ruleBlock = StatementBlockSymbol::fromSyntax(*result, *rule);
        result->addMember(ruleBlock);
    }

    return *result;
}

span<const RandSeqProductionSymbol::Rule> RandSeqProductionSymbol::getRules() const {
    if (!rules) {
        auto syntax = getSyntax();
        ASSERT(syntax);

        BindContext context(*this, LookupLocation::max);

        auto blocks = membersOfType<StatementBlockSymbol>();
        auto blockIt = blocks.begin();

        SmallVectorSized<Rule, 8> buffer;
        for (auto rule : syntax->as<ProductionSyntax>().rules) {
            ASSERT(blockIt != blocks.end());
            buffer.append(createRule(*rule, context, *blockIt++));
        }

        rules = buffer.copy(context.getCompilation());
    }
    return *rules;
}

const RandSeqProductionSymbol* RandSeqProductionSymbol::findProduction(string_view name,
                                                                       SourceRange nameRange,
                                                                       const BindContext& context) {
    auto symbol = Lookup::unqualifiedAt(*context.scope, name, context.getLocation(), nameRange,
                                        LookupFlags::AllowDeclaredAfter);
    if (!symbol)
        return nullptr;

    if (symbol->kind != SymbolKind::RandSeqProduction) {
        auto& diag = context.addDiag(diag::NotAProduction, nameRange) << name;
        diag.addNote(diag::NoteDeclarationHere, symbol->location);
        return nullptr;
    }

    return &symbol->as<RandSeqProductionSymbol>();
}

RandSeqProductionSymbol::ProdItem RandSeqProductionSymbol::createProdItem(
    const RsProdItemSyntax& syntax, const BindContext& context) {

    auto symbol = findProduction(syntax.name.valueText(), syntax.name.range(), context);
    if (!symbol)
        return ProdItem(nullptr, {});

    SmallVectorSized<const Expression*, 8> args;
    CallExpression::bindArgs(syntax.argList, symbol->arguments, symbol->name, syntax.sourceRange(),
                             context, args);

    return ProdItem(symbol, args.copy(context.getCompilation()));
}

const RandSeqProductionSymbol::CaseProd& RandSeqProductionSymbol::createCaseProd(
    const RsCaseSyntax& syntax, const BindContext& context) {

    SmallVectorSized<const ExpressionSyntax*, 8> expressions;
    SmallVectorSized<ProdItem, 8> prods;
    optional<ProdItem> defItem;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardRsCaseItem: {
                auto& sci = item->as<StandardRsCaseItemSyntax>();
                auto pi = createProdItem(*sci.item, context);
                for (auto es : sci.expressions) {
                    expressions.append(es);
                    prods.append(pi);
                }
                break;
            }
            case SyntaxKind::DefaultRsCaseItem:
                // The parser already errored for duplicate defaults,
                // so just ignore if it happens here.
                if (!defItem)
                    defItem = createProdItem(*item->as<DefaultRsCaseItemSyntax>().item, context);
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    SmallVectorSized<const Expression*, 8> bound;
    Expression::bindMembershipExpressions(context, TokenKind::CaseKeyword,
                                          /* requireIntegral */ false,
                                          /* unwrapUnpacked */ false,
                                          /* allowTypeReferences */ true, /* allowOpenRange */ true,
                                          *syntax.expr, expressions, bound);

    SmallVectorSized<CaseItem, 8> items;
    SmallVectorSized<const Expression*, 8> group;
    auto& comp = context.getCompilation();
    auto boundIt = bound.begin();
    auto prodIt = prods.begin();
    auto expr = *boundIt++;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardRsCaseItem: {
                auto& sci = item->as<StandardRsCaseItemSyntax>();
                for (size_t i = 0; i < sci.expressions.size(); i++)
                    group.append(*boundIt++);

                items.append({ group.copy(comp), *prodIt++ });
                group.clear();
                break;
            }
            default:
                break;
        }
    }

    return *comp.emplace<CaseProd>(*expr, items.copy(comp), defItem);
}

RandSeqProductionSymbol::Rule RandSeqProductionSymbol::createRule(
    const RsRuleSyntax& syntax, const BindContext& context, const StatementBlockSymbol& ruleBlock) {

    auto blockRange = ruleBlock.membersOfType<StatementBlockSymbol>();
    auto blockIt = blockRange.begin();

    auto& comp = context.getCompilation();
    SmallVectorSized<const ProdBase*, 8> prods;
    for (auto p : syntax.prods) {
        switch (p->kind) {
            case SyntaxKind::RsProdItem:
                prods.append(
                    comp.emplace<ProdItem>(createProdItem(p->as<RsProdItemSyntax>(), context)));
                break;
            case SyntaxKind::RsCodeBlock: {
                ASSERT(blockIt != blockRange.end());
                prods.append(comp.emplace<CodeBlockProd>(*blockIt++));
                break;
            }
            case SyntaxKind::RsIfElse: {
                auto& ries = p->as<RsIfElseSyntax>();
                auto& expr = Expression::bind(*ries.condition, context);
                auto ifItem = createProdItem(*ries.ifItem, context);

                optional<ProdItem> elseItem;
                if (ries.elseClause)
                    elseItem = createProdItem(*ries.elseClause->item, context);

                if (!expr.bad())
                    context.requireBooleanConvertible(expr);

                prods.append(comp.emplace<IfElseProd>(expr, ifItem, elseItem));
                break;
            }
            case SyntaxKind::RsRepeat: {
                auto& rrs = p->as<RsRepeatSyntax>();
                auto& expr = Expression::bind(*rrs.expr, context);
                auto item = createProdItem(*rrs.item, context);
                prods.append(comp.emplace<RepeatProd>(expr, item));

                if (!expr.bad() && !expr.type->isIntegral())
                    context.addDiag(diag::ExprMustBeIntegral, expr.sourceRange) << *expr.type;

                break;
            }
            case SyntaxKind::RsCase:
                prods.append(&createCaseProd(p->as<RsCaseSyntax>(), context));
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    const Expression* weightExpr = nullptr;
    optional<CodeBlockProd> codeBlock;
    if (auto wc = syntax.weightClause) {
        weightExpr = &Expression::bind(*wc->weight, context);
        if (!weightExpr->bad() && !weightExpr->type->isIntegral())
            context.addDiag(diag::ExprMustBeIntegral, weightExpr->sourceRange) << *weightExpr->type;

        if (wc->codeBlock) {
            ASSERT(blockIt != blockRange.end());
            codeBlock = CodeBlockProd(*blockIt++);
        }
    }

    bool isRandJoin = false;
    const Expression* randJoinExpr = nullptr;
    if (syntax.randJoin) {
        isRandJoin = true;
        if (syntax.randJoin->expr) {
            randJoinExpr = &Expression::bind(*syntax.randJoin->expr, context);

            if (!randJoinExpr->bad() && !randJoinExpr->type->isNumeric()) {
                context.addDiag(diag::RandJoinNotNumeric, randJoinExpr->sourceRange)
                    << *randJoinExpr->type;
            }
        }
    }

    return { ruleBlock, prods.copy(comp), weightExpr, randJoinExpr, codeBlock, isRandJoin };
}

void RandSeqProductionSymbol::createRuleVariables(const RsRuleSyntax& syntax, const Scope& scope,
                                                  SmallVector<const Symbol*>& results) {
    SmallMap<const RandSeqProductionSymbol*, uint32_t, 8> prodMap;
    auto countProd = [&](const RsProdItemSyntax& item) {
        auto symbol =
            Lookup::unqualified(scope, item.name.valueText(), LookupFlags::AllowDeclaredAfter);
        if (symbol && symbol->kind == SymbolKind::RandSeqProduction) {
            auto& prod = symbol->as<RandSeqProductionSymbol>();
            auto& type = prod.getReturnType();
            if (!type.isVoid()) {
                auto [it, inserted] = prodMap.emplace(&prod, 1);
                if (!inserted)
                    it->second++;
            }
        }
    };

    for (auto p : syntax.prods) {
        switch (p->kind) {
            case SyntaxKind::RsProdItem:
                countProd(p->as<RsProdItemSyntax>());
                break;
            case SyntaxKind::RsCodeBlock:
                break;
            case SyntaxKind::RsIfElse: {
                auto& ries = p->as<RsIfElseSyntax>();
                countProd(*ries.ifItem);
                if (ries.elseClause)
                    countProd(*ries.elseClause->item);
                break;
            }
            case SyntaxKind::RsRepeat:
                countProd(*p->as<RsRepeatSyntax>().item);
                break;
            case SyntaxKind::RsCase:
                for (auto item : p->as<RsCaseSyntax>().items) {
                    switch (item->kind) {
                        case SyntaxKind::StandardRsCaseItem:
                            countProd(*item->as<StandardRsCaseItemSyntax>().item);
                            break;
                        case SyntaxKind::DefaultRsCaseItem:
                            countProd(*item->as<DefaultRsCaseItemSyntax>().item);
                            break;
                        default:
                            THROW_UNREACHABLE;
                    }
                }
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    auto& comp = scope.getCompilation();
    for (auto [symbol, count] : prodMap) {
        auto var = comp.emplace<VariableSymbol>(symbol->name, syntax.getFirstToken().location(),
                                                VariableLifetime::Automatic);
        var->isCompilerGenerated = true;
        var->isConstant = true;

        if (count == 1) {
            var->setType(symbol->getReturnType());
        }
        else {
            ConstantRange range{ 1, int32_t(count) };
            var->setType(
                FixedSizeUnpackedArrayType::fromDims(comp, symbol->getReturnType(), { &range, 1 }));
        }

        results.append(var);
    }
}

void RandSeqProductionSymbol::serializeTo(ASTSerializer& serializer) const {
    auto writeItem = [&](string_view propName, const ProdItem& item) {
        serializer.writeProperty(propName);
        serializer.startObject();
        if (item.target)
            serializer.writeLink("target", *item.target);

        serializer.startArray("args");
        for (auto arg : item.args)
            serializer.serialize(*arg);
        serializer.endArray();

        serializer.endObject();
    };

    serializer.write("returnType", getReturnType());

    serializer.startArray("arguments");
    for (auto arg : arguments)
        serializer.serialize(*arg);
    serializer.endArray();

    serializer.startArray("rules");
    for (auto& rule : getRules()) {
        serializer.startObject();

        serializer.startArray("prods");
        for (auto prod : rule.prods) {
            serializer.startObject();
            switch (prod->kind) {
                case ProdKind::Item:
                    serializer.write("kind", "Item"sv);
                    writeItem("item", *(const ProdItem*)prod);
                    break;
                case ProdKind::CodeBlock:
                    serializer.write("kind", "CodeBlock"sv);
                    break;
                case ProdKind::IfElse: {
                    auto& iep = *(const IfElseProd*)prod;
                    serializer.write("kind", "IfElse"sv);
                    serializer.write("expr", *iep.expr);

                    writeItem("ifItem", iep.ifItem);
                    if (iep.elseItem)
                        writeItem("elseItem", *iep.elseItem);
                    break;
                }
                case ProdKind::Repeat: {
                    auto& rp = *(const RepeatProd*)prod;
                    serializer.write("kind", "Repeat"sv);
                    serializer.write("expr", *rp.expr);
                    writeItem("item", rp.item);
                    break;
                }
                case ProdKind::Case: {
                    auto& cp = *(const CaseProd*)prod;
                    serializer.write("kind", "Case"sv);
                    serializer.write("expr", *cp.expr);
                    if (cp.defaultItem)
                        writeItem("defaultItem", *cp.defaultItem);

                    serializer.startArray("items");
                    for (auto& item : cp.items) {
                        serializer.startObject();
                        serializer.startArray("expressions");
                        for (auto expr : item.expressions)
                            serializer.serialize(*expr);
                        serializer.endArray();

                        writeItem("item", item.item);
                        serializer.endObject();
                    }
                    serializer.endArray();
                    break;
                }
                default:
                    THROW_UNREACHABLE;
            }
            serializer.endObject();
        }
        serializer.endArray();

        if (rule.weightExpr)
            serializer.write("weightExpr", *rule.weightExpr);

        serializer.write("isRandJoin", rule.isRandJoin);
        if (rule.randJoinExpr)
            serializer.write("randJoinExpr", *rule.randJoinExpr);

        serializer.endObject();
    }
    serializer.endArray();
}

} // namespace slang
