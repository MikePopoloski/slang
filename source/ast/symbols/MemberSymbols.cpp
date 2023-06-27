//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/MemberSymbols.h"

#include "../FmtHelpers.h"
#include "fmt/core.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/String.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

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

static const PackageSymbol* findPackage(std::string_view packageName, const Scope& lookupScope,
                                        SourceLocation errorLoc) {
    auto& comp = lookupScope.getCompilation();
    auto package = comp.getPackage(packageName);
    if (!package && !packageName.empty() && !comp.getOptions().lintMode)
        lookupScope.addDiag(diag::UnknownPackage, errorLoc) << packageName;
    return package;
}

const Symbol* ExplicitImportSymbol::importedSymbol() const {
    if (!initialized) {
        initialized = true;

        const Scope* scope = getParentScope();
        SLANG_ASSERT(scope);

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
                diag << importName << packageName;
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
        SLANG_ASSERT(scope);

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

ModportPortSymbol::ModportPortSymbol(std::string_view name, SourceLocation loc,
                                     ArgumentDirection direction) :
    ValueSymbol(SymbolKind::ModportPort, name, loc),
    direction(direction) {
}

ModportPortSymbol& ModportPortSymbol::fromSyntax(const ASTContext& context,
                                                 ArgumentDirection direction,
                                                 const ModportNamedPortSyntax& syntax) {
    auto& comp = context.getCompilation();
    auto name = syntax.name;
    auto result = comp.emplace<ModportPortSymbol>(name.valueText(), name.location(), direction);
    result->setSyntax(syntax);
    result->internalSymbol = Lookup::unqualifiedAt(*context.scope, name.valueText(),
                                                   context.getLocation(), name.range(),
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

    if (!result->internalSymbol) {
        result->setType(comp.getErrorType());
        return *result;
    }

    auto sourceType = result->internalSymbol->getDeclaredType();
    SLANG_ASSERT(sourceType);
    result->getDeclaredType()->setLink(*sourceType);

    // Perform checking on the connected symbol to make sure it's allowed
    // given the modport's direction.
    ASTContext checkCtx = context.resetFlags(ASTFlags::NonProcedural | ASTFlags::NotADriver);
    if (direction != ArgumentDirection::In)
        checkCtx.flags |= ASTFlags::LValue;

    auto loc = result->location;
    auto& expr = ValueExpressionBase::fromSymbol(checkCtx, *result->internalSymbol, false,
                                                 {loc, loc + result->name.length()});

    Expression::checkConnectionDirection(expr, direction, checkCtx, loc);

    result->connExpr = &expr;
    return *result;
}

ModportPortSymbol& ModportPortSymbol::fromSyntax(const ASTContext& parentContext,
                                                 ArgumentDirection direction,
                                                 const ModportExplicitPortSyntax& syntax) {
    ASTContext context = parentContext.resetFlags(ASTFlags::NonProcedural | ASTFlags::NotADriver);
    auto& comp = context.getCompilation();
    auto name = syntax.name;
    auto result = comp.emplace<ModportPortSymbol>(name.valueText(), name.location(), direction);
    result->setSyntax(syntax);

    if (!syntax.expr) {
        result->setType(comp.getVoidType());
        return *result;
    }

    ASTFlags extraFlags = ASTFlags::None;
    if (direction == ArgumentDirection::Out || direction == ArgumentDirection::InOut)
        extraFlags = ASTFlags::LValue;

    auto& expr = Expression::bind(*syntax.expr, context, extraFlags);
    result->explicitConnection = &expr;
    result->connExpr = &expr;
    if (expr.bad()) {
        result->setType(comp.getErrorType());
        return *result;
    }

    result->setType(*expr.type);

    Expression::checkConnectionDirection(expr, direction, context, result->location);

    return *result;
}

void ModportPortSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("direction", toString(direction));
    if (internalSymbol)
        serializer.writeLink("internalSymbol", *internalSymbol);
    if (explicitConnection)
        serializer.write("explicitConnection", *explicitConnection);
}

ModportClockingSymbol::ModportClockingSymbol(std::string_view name, SourceLocation loc) :
    Symbol(SymbolKind::ModportClocking, name, loc) {
}

ModportClockingSymbol& ModportClockingSymbol::fromSyntax(const ASTContext& context,
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

ModportSymbol::ModportSymbol(Compilation& compilation, std::string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Modport, name, loc), Scope(compilation, this) {
}

void ModportSymbol::fromSyntax(const ASTContext& context, const ModportDeclarationSyntax& syntax,
                               SmallVectorBase<const ModportSymbol*>& results) {
    auto& comp = context.getCompilation();
    for (auto item : syntax.items) {
        auto modport = comp.emplace<ModportSymbol>(comp, item->name.valueText(),
                                                   item->name.location());
        modport->setSyntax(*item);
        modport->setAttributes(*context.scope, syntax.attributes);
        results.push_back(modport);

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
                            case SyntaxKind::ModportExplicitPort: {
                                auto& mpp = ModportPortSymbol::fromSyntax(
                                    context, direction,
                                    simplePort->as<ModportExplicitPortSyntax>());
                                mpp.setAttributes(*modport, portList.attributes);
                                modport->addMember(mpp);
                                break;
                            }
                            default:
                                SLANG_UNREACHABLE;
                        }
                    }
                    break;
                }
                case SyntaxKind::ModportSubroutinePortList: {
                    auto& portList = port->as<ModportSubroutinePortListSyntax>();
                    bool isExport = portList.importExport.kind == TokenKind::ExportKeyword;
                    if (isExport)
                        modport->hasExports = true;

                    for (auto subPort : portList.ports) {
                        switch (subPort->kind) {
                            case SyntaxKind::ModportNamedPort: {
                                auto& mps = MethodPrototypeSymbol::fromSyntax(
                                    context, subPort->as<ModportNamedPortSyntax>(), isExport);
                                mps.setAttributes(*modport, portList.attributes);
                                modport->addMember(mps);
                                break;
                            }
                            case SyntaxKind::ModportSubroutinePort: {
                                auto& mps = MethodPrototypeSymbol::fromSyntax(
                                    *context.scope, subPort->as<ModportSubroutinePortSyntax>(),
                                    isExport);
                                mps.setAttributes(*modport, portList.attributes);
                                modport->addMember(mps);
                                break;
                            }
                            default:
                                SLANG_UNREACHABLE;
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
                    SLANG_UNREACHABLE;
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
                                        const ASTContext& parentContext,
                                        SmallVectorBase<const Symbol*>& results,
                                        SmallVectorBase<const Symbol*>& implicitNets) {
    ASTContext context = parentContext.resetFlags(ASTFlags::NonProcedural);
    auto& netType = context.scope->getDefaultNetType();
    SmallSet<std::string_view, 8> seenNames;

    for (auto expr : syntax.assignments) {
        // If not explicitly disabled, check for net references on the lhs of each
        // assignment that should create implicit nets.
        if (!netType.isError()) {
            // The expression here should always be an assignment expression unless
            // the program is already ill-formed (diagnosed by the parser).
            if (expr->kind == SyntaxKind::AssignmentExpression) {
                SmallVector<const IdentifierNameSyntax*> implicitNetNames;
                Expression::findPotentiallyImplicitNets(*expr->as<BinaryExpressionSyntax>().left,
                                                        context, implicitNetNames);

                for (auto ins : implicitNetNames) {
                    if (seenNames.emplace(ins->identifier.valueText()).second) {
                        implicitNets.push_back(
                            &NetSymbol::createImplicit(compilation, *ins, netType));
                    }
                }
            }
        }

        auto symbol = compilation.emplace<ContinuousAssignSymbol>(*expr);
        symbol->setAttributes(*context.scope, syntax.attributes);
        results.push_back(symbol);
    }
}

const Expression& ContinuousAssignSymbol::getAssignment() const {
    if (assign)
        return *assign;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    SLANG_ASSERT(scope && syntax);

    ASTContext context(*scope, LookupLocation::after(*this), ASTFlags::NonProcedural);
    assign = &Expression::bind(syntax->as<ExpressionSyntax>(), context,
                               ASTFlags::AssignmentAllowed);

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
                    if constexpr (HasVisitExprs<T, ExpressionVarVisitor>) {
                        expr.visitExprs(*this);
                    }
                    break;
            }
        }
    }
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

    ASTContext context(*scope, LookupLocation::before(*this), ASTFlags::NonProcedural);
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

std::pair<std::optional<DriveStrength>, std::optional<DriveStrength>> ContinuousAssignSymbol::
    getDriveStrength() const {
    auto syntax = getSyntax();
    if (syntax && syntax->parent) {
        auto& cas = syntax->parent->as<ContinuousAssignSyntax>();
        if (cas.strength)
            return SemanticFacts::getDriveStrength(*cas.strength);
    }
    return {};
}

void ContinuousAssignSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("assignment", getAssignment());

    if (auto delayCtrl = getDelay())
        serializer.write("delay", *delayCtrl);

    auto [ds0, ds1] = getDriveStrength();
    if (ds0)
        serializer.write("driveStrength0", toString(*ds0));
    if (ds1)
        serializer.write("driveStrength1", toString(*ds1));
}

GenvarSymbol::GenvarSymbol(std::string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Genvar, name, loc) {
}

void GenvarSymbol::fromSyntax(const Scope& parent, const GenvarDeclarationSyntax& syntax,
                              SmallVectorBase<const GenvarSymbol*>& results) {
    auto& comp = parent.getCompilation();
    for (auto id : syntax.identifiers) {
        auto name = id->identifier;
        if (name.valueText().empty())
            continue;

        auto genvar = comp.emplace<GenvarSymbol>(name.valueText(), name.location());
        genvar->setSyntax(*id);
        genvar->setAttributes(parent, syntax.attributes);
        results.push_back(genvar);
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

std::optional<std::string_view> ElabSystemTaskSymbol::getMessage() const {
    if (resolved)
        return message;

    resolved = true;

    auto syntax = getSyntax();
    SLANG_ASSERT(syntax);

    auto argSyntax = syntax->as<ElabSystemTaskSyntax>().arguments;
    if (!argSyntax) {
        message = "";
        return message;
    }

    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    // Bind all arguments.
    auto& comp = scope->getCompilation();
    ASTContext astCtx(*scope, LookupLocation::before(*this));
    SmallVector<const Expression*> args;
    for (auto arg : argSyntax->parameters) {
        switch (arg->kind) {
            case SyntaxKind::OrderedArgument: {
                const auto& oa = arg->as<OrderedArgumentSyntax>();
                if (auto exSyn = astCtx.requireSimpleExpr(*oa.expr))
                    args.push_back(&Expression::bind(*exSyn, astCtx));
                else
                    return {};
                break;
            }
            case SyntaxKind::NamedArgument:
                astCtx.addDiag(diag::NamedArgNotAllowed, arg->sourceRange());
                return {};
            case SyntaxKind::EmptyArgument:
                args.push_back(
                    comp.emplace<EmptyArgumentExpression>(comp.getVoidType(), arg->sourceRange()));
                break;
            default:
                SLANG_UNREACHABLE;
        }

        if (args.back()->bad())
            return {};
    }

    std::span<const Expression* const> argSpan = args;
    if (!argSpan.empty()) {
        if (taskKind == ElabSystemTaskKind::Fatal) {
            // If this is a $fatal task, check the finish number. We don't use this
            // for anything, but enforce that it's 0, 1, or 2.
            if (!FmtHelpers::checkFinishNum(astCtx, *argSpan[0]))
                return {};

            argSpan = argSpan.subspan(1);
        }
        else if (taskKind == ElabSystemTaskKind::StaticAssert) {
            // The first argument is the condition to check.
            if (!astCtx.requireBooleanConvertible(*argSpan[0]) || !astCtx.eval(*argSpan[0]))
                return {};

            assertCondition = argSpan[0];
            argSpan = argSpan.subspan(1);
        }
    }

    message = createMessage(astCtx, argSpan);
    return message;
}

std::optional<std::string_view> ElabSystemTaskSymbol::createMessage(
    const ASTContext& context, std::span<const Expression* const> args) {

    // Check all arguments.
    if (!FmtHelpers::checkDisplayArgs(context, args))
        return {};

    // Format the message to string.
    auto& comp = context.getCompilation();
    EvalContext evalCtx(comp);
    std::optional<std::string> str = FmtHelpers::formatDisplay(*context.scope, evalCtx, args);
    evalCtx.reportDiags(context);

    if (!str)
        return {};

    if (str->empty())
        return ""sv;

    str->insert(0, ": ");

    // Copy the string into permanent memory.
    auto mem = comp.allocate(str->size(), alignof(char));
    memcpy(mem, str->data(), str->size());

    return std::string_view(reinterpret_cast<char*>(mem), str->size());
}

static void reduceComparison(const BinaryExpression& expr, Diagnostic& result) {
    switch (expr.op) {
        case BinaryOperator::Equality:
        case BinaryOperator::Inequality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::CaseInequality:
        case BinaryOperator::WildcardEquality:
        case BinaryOperator::WildcardInequality:
        case BinaryOperator::GreaterThan:
        case BinaryOperator::GreaterThanEqual:
        case BinaryOperator::LessThan:
        case BinaryOperator::LessThanEqual:
            break;
        default:
            return;
    }

    SLANG_ASSERT(expr.syntax);
    auto& syntax = expr.syntax->as<BinaryExpressionSyntax>();

    auto lc = expr.left().constant;
    auto rc = expr.right().constant;
    SLANG_ASSERT(lc && rc);

    auto& note = result.addNote(diag::NoteComparisonReduces, syntax.operatorToken.location());
    note << expr.sourceRange;
    note << *lc << syntax.operatorToken.rawText() << *rc;
}

void ElabSystemTaskSymbol::reportStaticAssert(const Scope& scope, SourceLocation loc,
                                              std::string_view message,
                                              const Expression* condition) {
    if (condition && condition->constant) {
        // Issue no diagnostic if the assert condition is true.
        if (condition->constant->isTrue())
            return;
    }

    auto& diag = scope.addDiag(diag::StaticAssert, loc).addStringAllowEmpty(std::string(message));

    // If the condition is a comparison operator, note the value of both
    // sides to provide more info about why the assertion failed.
    if (condition && condition->kind == ExpressionKind::BinaryOp)
        reduceComparison(condition->as<BinaryExpression>(), diag);
}

void ElabSystemTaskSymbol::issueDiagnostic() const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto msg = getMessage();
    if (!msg)
        return;

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
        case ElabSystemTaskKind::StaticAssert:
            reportStaticAssert(*scope, location, *msg, assertCondition);
            return;
        default:
            SLANG_UNREACHABLE;
    }

    scope->addDiag(code, location).addStringAllowEmpty(std::string(*msg));
}

const Expression* ElabSystemTaskSymbol::getAssertCondition() const {
    getMessage();
    return assertCondition;
}

void ElabSystemTaskSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("taskKind", toString(taskKind));

    if (auto msg = getMessage())
        serializer.write("message", *msg);

    if (assertCondition)
        serializer.write("assertCondition", *assertCondition);
}

PrimitivePortSymbol::PrimitivePortSymbol(Compilation& compilation, std::string_view name,
                                         SourceLocation loc, PrimitivePortDirection direction) :
    ValueSymbol(SymbolKind::PrimitivePort, name, loc),
    direction(direction) {
    // All primitive ports are single bit logic types.
    setType(compilation.getLogicType());
}

void PrimitivePortSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("direction", toString(direction));
}

static char getUdpFieldChar(const UdpFieldBaseSyntax* base) {
    if (base && base->kind == SyntaxKind::UdpSimpleField) {
        auto raw = base->as<UdpSimpleFieldSyntax>().field.rawText();
        if (!raw.empty())
            return raw[0];
    }
    return 0;
}

static void expandTableEntries(const Scope& scope, const UdpEntrySyntax& syntax,
                               const SmallVector<PrimitiveSymbol::TableField>& fields,
                               SmallVector<PrimitiveSymbol::TableField>& currEntry,
                               size_t fieldIndex, PrimitiveSymbol::TableEntry& baseEntry,
                               SmallVector<PrimitiveSymbol::TableEntry>& results,
                               SmallMap<std::string, const UdpEntrySyntax*, 4>& rowDupMap) {
    if (fieldIndex == fields.size()) {
        // Build a key out of inputs and current state (if present) that
        // let us determine if this combination has already been added to the table.
        std::string key;
        bool allX = true;
        for (auto& field : currEntry) {
            allX &= charToLower(field.value) == 'x';
            if (field.transitionTo) {
                key.push_back('(');
                key.push_back(field.value);
                key.push_back(field.transitionTo);
                key.push_back(')');
                allX &= charToLower(field.transitionTo) == 'x';
            }
            else {
                key.push_back(field.value);
            }
        }

        if (baseEntry.state.value)
            key.push_back(baseEntry.state.value);

        auto [it, inserted] = rowDupMap.emplace(std::move(key), &syntax);
        if (!inserted) {
            // This is an error if the existing row has a different output,
            // otherwise it's just silently ignored.
            auto existing = getUdpFieldChar(it->second->next);
            if (existing != baseEntry.output.value && existing && baseEntry.output.value) {
                auto& diag = scope.addDiag(diag::UdpDupDiffOutput, syntax.sourceRange());
                diag.addNote(diag::NotePreviousDefinition, it->second->sourceRange());
            }
        }
        else {
            if (allX && !currEntry.empty() && charToLower(baseEntry.output.value) != 'x')
                scope.addDiag(diag::UdpAllX, syntax.sourceRange());

            baseEntry.inputs = currEntry.copy(scope.getCompilation());
            results.push_back(baseEntry);
        }
        return;
    }

    auto next = [&](SmallVector<PrimitiveSymbol::TableField>& nextFieldList) {
        expandTableEntries(scope, syntax, fields, nextFieldList, fieldIndex + 1, baseEntry, results,
                           rowDupMap);
    };

    auto& field = fields[fieldIndex];
    const char v = charToLower(field.value);

    if (field.transitionTo) {
        const char w = charToLower(field.transitionTo);

        SmallVector<char> firstChars;
        SmallVector<char> secondChars;
        for (int i = 0; i < 2; i++) {
            auto currVec = i ? &secondChars : &firstChars;
            auto c = i ? w : v;
            switch (c) {
                case '?':
                    for (auto d : {'0', '1', 'x'})
                        currVec->push_back(d);
                    break;
                case 'b':
                    for (auto d : {'0', '1'})
                        currVec->push_back(d);
                    break;
                default:
                    currVec->push_back(c);
                    break;
            }
        }

        for (auto c : firstChars) {
            for (auto d : secondChars) {
                // Don't insert invalid double-x transition entries
                // even if the expansion of an iteration character would
                // otherwise cause us to do so.
                if (c == 'x' && d == 'x')
                    continue;

                auto copiedEntry = currEntry;
                copiedEntry.push_back({c, d});
                next(copiedEntry);
            }
        }
    }
    else {
        switch (v) {
            case '?':
                for (auto c : {'0', '1', 'x'}) {
                    auto copiedEntry = currEntry;
                    copiedEntry.push_back({c});
                    next(copiedEntry);
                }
                break;
            case 'b':
                for (auto c : {'0', '1'}) {
                    auto copiedEntry = currEntry;
                    copiedEntry.push_back({c});
                    next(copiedEntry);
                }
                break;
            case 'p':
                for (auto c : {"01", "0x", "x1"}) {
                    auto copiedEntry = currEntry;
                    copiedEntry.push_back({c[0], c[1]});
                    next(copiedEntry);
                }
                break;
            case 'n':
                for (auto c : {"10", "1x", "x0"}) {
                    auto copiedEntry = currEntry;
                    copiedEntry.push_back({c[0], c[1]});
                    next(copiedEntry);
                }
                break;
            case '*':
                for (auto c : {"01", "0x", "x1", "10", "1x", "x0"}) {
                    auto copiedEntry = currEntry;
                    copiedEntry.push_back({c[0], c[1]});
                    next(copiedEntry);
                }
                break;
            case 'r':
                currEntry.push_back({'0', '1'});
                next(currEntry);
                break;
            case 'f':
                currEntry.push_back({'1', '0'});
                next(currEntry);
                break;
            default:
                currEntry.push_back({v});
                next(currEntry);
                break;
        }
    }
}

static void createTableEntries(const Scope& scope, const UdpEntrySyntax& syntax,
                               SmallVector<PrimitiveSymbol::TableEntry>& results,
                               SmallMap<std::string, const UdpEntrySyntax*, 4>& rowDupMap,
                               size_t numPorts) {
    SmallVector<PrimitiveSymbol::TableField> fields;
    for (auto input : syntax.inputs) {
        if (input->kind == SyntaxKind::UdpEdgeField) {
            auto& edge = input->as<UdpEdgeFieldSyntax>();

            SmallVector<char, 4> chars;
            chars.append_range(edge.first.rawText());
            chars.append_range(edge.second.rawText());

            PrimitiveSymbol::TableField field;
            if (chars.size() > 0)
                field.value = chars[0];
            if (chars.size() > 1)
                field.transitionTo = chars[1];

            fields.push_back(field);
        }
        else {
            auto tok = input->as<UdpSimpleFieldSyntax>().field;
            for (auto c : tok.rawText())
                fields.push_back({c, 0});
        }
    }

    if (numPorts >= 2 && fields.size() != numPorts - 1) {
        auto& diag = scope.addDiag(diag::UdpWrongInputCount, syntax.inputs.sourceRange());
        diag << fields.size();
        diag << numPorts - 1;
    }

    PrimitiveSymbol::TableEntry entry;
    entry.state.value = getUdpFieldChar(syntax.current);
    entry.output.value = getUdpFieldChar(syntax.next);

    SmallVector<PrimitiveSymbol::TableField> currEntry;
    expandTableEntries(scope, syntax, fields, currEntry, 0, entry, results, rowDupMap);
}

PrimitiveSymbol& PrimitiveSymbol::fromSyntax(const Scope& scope,
                                             const UdpDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto primName = syntax.name.valueText();
    auto prim = comp.emplace<PrimitiveSymbol>(comp, primName, syntax.name.location(),
                                              PrimitiveSymbol::UserDefined);
    prim->setAttributes(scope, syntax.attributes);
    prim->setSyntax(syntax);

    auto portList = syntax.portList.get();
    if (portList->kind == SyntaxKind::WildcardUdpPortList) {
        auto externPrim = comp.getExternPrimitive(primName, scope);
        if (!externPrim)
            scope.addDiag(diag::MissingExternWildcardPorts, portList->sourceRange()) << primName;
        else
            portList = externPrim->portList;
    }

    SmallVector<const PrimitivePortSymbol*> ports;
    if (portList->kind == SyntaxKind::AnsiUdpPortList) {
        for (auto decl : portList->as<AnsiUdpPortListSyntax>().ports) {
            if (decl->kind == SyntaxKind::UdpOutputPortDecl) {
                auto& outputDecl = decl->as<UdpOutputPortDeclSyntax>();
                PrimitivePortDirection dir = PrimitivePortDirection::Out;
                if (outputDecl.reg)
                    dir = PrimitivePortDirection::OutReg;

                auto port = comp.emplace<PrimitivePortSymbol>(comp, outputDecl.name.valueText(),
                                                              outputDecl.name.location(), dir);
                port->setSyntax(*decl);
                port->setAttributes(scope, decl->attributes);
                ports.push_back(port);
                prim->addMember(*port);
            }
            else {
                auto& inputDecl = decl->as<UdpInputPortDeclSyntax>();
                for (auto nameSyntax : inputDecl.names) {
                    auto name = nameSyntax->identifier;
                    auto port = comp.emplace<PrimitivePortSymbol>(comp, name.valueText(),
                                                                  name.location(),
                                                                  PrimitivePortDirection::In);

                    port->setSyntax(*nameSyntax);
                    port->setAttributes(scope, decl->attributes);
                    ports.push_back(port);
                    prim->addMember(*port);
                }
            }
        }

        if (!syntax.body->portDecls.empty())
            scope.addDiag(diag::PrimitiveAnsiMix, syntax.body->portDecls[0]->sourceRange());
    }
    else if (portList->kind == SyntaxKind::NonAnsiUdpPortList) {
        // In the non-ansi case the port list only gives the ordering, we need to
        // look through the body decls to get the rest of the port info.
        SmallMap<std::string_view, PrimitivePortSymbol*, 4> portMap;
        for (auto nameSyntax : portList->as<NonAnsiUdpPortListSyntax>().ports) {
            auto name = nameSyntax->identifier;
            auto port = comp.emplace<PrimitivePortSymbol>(comp, name.valueText(), name.location(),
                                                          PrimitivePortDirection::In);
            ports.push_back(port);
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
                            auto& diag = scope.addDiag(diag::PrimitiveRegDup,
                                                       outputDecl.reg.range());
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
            SLANG_ASSERT(it != portMap.end());

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
    else {
        // This is an error condition (wildcard port list without a
        // corresponding extern decl). The error has already been
        // issued so just get out of here.
        return *prim;
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
            ASTContext context(scope, LookupLocation::max);
            auto& expr = Expression::bind(*initExpr, context);
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

    SmallMap<std::string, const UdpEntrySyntax*, 4> rowDupMap;
    SmallVector<TableEntry> table;
    for (auto entry : syntax.body->entries)
        createTableEntries(scope, *entry, table, rowDupMap, ports.size());

    prim->ports = ports.copy(comp);
    prim->table = table.copy(comp);
    return *prim;
}

void PrimitiveSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("isSequential", isSequential);
    if (initVal)
        serializer.write("initVal", *initVal);

    if (!table.empty()) {
        serializer.startArray("table");
        for (auto& row : table) {
            serializer.startObject();
            serializer.startArray("inputs");
            for (auto& entry : row.inputs) {
                if (entry.transitionTo)
                    serializer.serialize(fmt::format("({}{})", entry.value, entry.transitionTo));
                else
                    serializer.serialize(std::string_view(&entry.value, 1));
            }
            serializer.endArray();
            if (row.state.value)
                serializer.write("state", std::string_view(&row.state.value, 1));
            serializer.write("output", std::string_view(&row.output.value, 1));
            serializer.endObject();
        }
        serializer.endArray();
    }
}

AssertionPortSymbol::AssertionPortSymbol(std::string_view name, SourceLocation loc) :
    Symbol(SymbolKind::AssertionPort, name, loc), declaredType(*this) {
}

static bool isEmptyType(const DataTypeSyntax& syntax) {
    if (syntax.kind != SyntaxKind::ImplicitType)
        return false;

    auto& implicit = syntax.as<ImplicitTypeSyntax>();
    return !implicit.signing && implicit.dimensions.empty();
}

void AssertionPortSymbol::buildPorts(Scope& scope, const AssertionItemPortListSyntax& syntax,
                                     SmallVectorBase<const AssertionPortSymbol*>& results) {
    auto& comp = scope.getCompilation();
    auto parentKind = scope.asSymbol().kind;
    auto& untyped = comp.getType(SyntaxKind::Untyped);
    const DataTypeSyntax* lastType = nullptr;
    std::optional<ArgumentDirection> lastDir;

    for (auto item : syntax.ports) {
        auto port = comp.emplace<AssertionPortSymbol>(item->name.valueText(),
                                                      item->name.location());
        port->setSyntax(*item);
        port->setAttributes(scope, item->attributes);

        if (!item->dimensions.empty())
            port->declaredType.setDimensionSyntax(item->dimensions);

        if (item->local) {
            port->direction = item->direction ? SemanticFacts::getDirection(item->direction.kind)
                                              : ArgumentDirection::In;

            // If we have a direction we can never inherit the previous type.
            lastType = nullptr;
        }
        else if (isEmptyType(*item->type)) {
            port->direction = lastDir;
        }

        // 'local' direction requires that we have a sequence type. This flag needs to be
        // added prior to setting a resolved type in the branches below.
        if (port->direction)
            port->declaredType.addFlags(DeclaredTypeFlags::RequireSequenceType);

        if (isEmptyType(*item->type)) {
            if (lastType)
                port->declaredType.setTypeSyntax(*lastType);
            else {
                port->declaredType.setType(untyped);
                if (!item->dimensions.empty()) {
                    scope.addDiag(diag::InvalidArrayElemType, item->dimensions.sourceRange())
                        << untyped;
                }

                if (item->local && parentKind != SymbolKind::LetDecl)
                    scope.addDiag(diag::LocalVarTypeRequired, item->local.range());
            }
        }
        else {
            port->declaredType.setTypeSyntax(*item->type);
            lastType = item->type;

            // Ports of type 'property' are not allowed in sequences,
            // and let declarations cannot have ports of type 'sequence' or 'property'.
            auto itemKind = item->type->kind;
            if (itemKind == SyntaxKind::PropertyType && parentKind == SymbolKind::Sequence) {
                scope.addDiag(diag::PropertyPortInSeq, item->type->sourceRange());
            }
            else if ((itemKind == SyntaxKind::PropertyType ||
                      itemKind == SyntaxKind::SequenceType) &&
                     parentKind == SymbolKind::LetDecl) {
                scope.addDiag(diag::PropertyPortInLet, item->type->sourceRange())
                    << item->type->getFirstToken().valueText();
            }
        }

        lastDir = port->direction;
        if (item->defaultValue) {
            if (port->direction == ArgumentDirection::Out ||
                port->direction == ArgumentDirection::InOut) {
                scope.addDiag(diag::AssertionPortOutputDefault,
                              item->defaultValue->expr->sourceRange());
            }
            else {
                port->defaultValueSyntax = item->defaultValue->expr;
            }
        }

        scope.addMember(*port);
        results.push_back(port);
    }
}

AssertionPortSymbol& AssertionPortSymbol::clone(Scope& newScope) const {
    auto& comp = newScope.getCompilation();
    auto result = comp.emplace<AssertionPortSymbol>(name, location);
    result->declaredType.setLink(declaredType);
    result->defaultValueSyntax = defaultValueSyntax;
    result->direction = direction;

    if (auto syntax = getSyntax()) {
        result->setSyntax(*syntax);
        result->setAttributes(newScope, syntax->as<AssertionItemPortSyntax>().attributes);
    }

    return *result;
}

void AssertionPortSymbol::serializeTo(ASTSerializer& serializer) const {
    if (direction)
        serializer.write("direction", toString(*direction));
}

SequenceSymbol::SequenceSymbol(Compilation& compilation, std::string_view name,
                               SourceLocation loc) :
    Symbol(SymbolKind::Sequence, name, loc),
    Scope(compilation, this) {
}

SequenceSymbol& SequenceSymbol::fromSyntax(const Scope& scope,
                                           const SequenceDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<SequenceSymbol>(comp, syntax.name.valueText(),
                                               syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    SmallVector<const AssertionPortSymbol*> ports;
    if (syntax.portList)
        AssertionPortSymbol::buildPorts(*result, *syntax.portList, ports);
    result->ports = ports.copy(comp);

    return *result;
}

void SequenceSymbol::makeDefaultInstance() const {
    AssertionInstanceExpression::makeDefault(*this);
}

PropertySymbol::PropertySymbol(Compilation& compilation, std::string_view name,
                               SourceLocation loc) :
    Symbol(SymbolKind::Property, name, loc),
    Scope(compilation, this) {
}

PropertySymbol& PropertySymbol::fromSyntax(const Scope& scope,
                                           const PropertyDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<PropertySymbol>(comp, syntax.name.valueText(),
                                               syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    SmallVector<const AssertionPortSymbol*> ports;
    if (syntax.portList)
        AssertionPortSymbol::buildPorts(*result, *syntax.portList, ports);
    result->ports = ports.copy(comp);

    return *result;
}

void PropertySymbol::makeDefaultInstance() const {
    AssertionInstanceExpression::makeDefault(*this);
}

LetDeclSymbol::LetDeclSymbol(Compilation& compilation, const ExpressionSyntax& exprSyntax,
                             std::string_view name, SourceLocation loc) :
    Symbol(SymbolKind::LetDecl, name, loc),
    Scope(compilation, this), exprSyntax(&exprSyntax) {
}

LetDeclSymbol& LetDeclSymbol::fromSyntax(const Scope& scope, const LetDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<LetDeclSymbol>(comp, *syntax.expr, syntax.identifier.valueText(),
                                              syntax.identifier.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    SmallVector<const AssertionPortSymbol*> ports;
    if (syntax.portList)
        AssertionPortSymbol::buildPorts(*result, *syntax.portList, ports);
    result->ports = ports.copy(comp);

    return *result;
}

void LetDeclSymbol::makeDefaultInstance() const {
    AssertionInstanceExpression::makeDefault(*this);
}

CheckerSymbol::CheckerSymbol(Compilation& compilation, std::string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Checker, name, loc), Scope(compilation, this) {
}

CheckerSymbol& CheckerSymbol::fromSyntax(const Scope& scope,
                                         const CheckerDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CheckerSymbol>(comp, syntax.name.valueText(),
                                              syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    SmallVector<const AssertionPortSymbol*> ports;
    if (syntax.portList) {
        // Checker port symbols differ enough in their rules that we
        // don't try to reuse buildPorts here.
        auto& untyped = comp.getType(SyntaxKind::Untyped);
        const DataTypeSyntax* lastType = nullptr;
        ArgumentDirection lastDir = ArgumentDirection::In;

        for (auto item : syntax.portList->ports) {
            auto port = comp.emplace<AssertionPortSymbol>(item->name.valueText(),
                                                          item->name.location());
            port->setSyntax(*item);
            port->setAttributes(scope, item->attributes);

            if (!item->dimensions.empty())
                port->declaredType.setDimensionSyntax(item->dimensions);

            if (item->local)
                scope.addDiag(diag::LocalNotAllowed, item->local.range());

            if (item->direction) {
                port->direction = SemanticFacts::getDirection(item->direction.kind);

                // If we have a direction we can never inherit the previous type.
                lastType = nullptr;
            }
            else {
                port->direction = lastDir;
            }

            if (isEmptyType(*item->type)) {
                if (lastType)
                    port->declaredType.setTypeSyntax(*lastType);
                else {
                    port->declaredType.setType(untyped);
                    if (!item->dimensions.empty()) {
                        scope.addDiag(diag::InvalidArrayElemType, item->dimensions.sourceRange())
                            << untyped;
                    }

                    if (item->direction)
                        scope.addDiag(diag::CheckerPortDirectionType, item->direction.range());
                }
            }
            else {
                port->declaredType.setTypeSyntax(*item->type);
                lastType = item->type;

                auto itemKind = item->type->kind;
                if (port->direction == ArgumentDirection::Out &&
                    (itemKind == SyntaxKind::PropertyType || itemKind == SyntaxKind::SequenceType ||
                     itemKind == SyntaxKind::Untyped)) {
                    scope.addDiag(diag::CheckerOutputBadType, item->type->sourceRange());
                    port->declaredType.setType(comp.getErrorType());
                }
            }

            lastDir = *port->direction;
            if (item->defaultValue)
                port->defaultValueSyntax = item->defaultValue->expr;

            result->addMember(*port);
            ports.push_back(port);
        }
    }
    result->ports = ports.copy(comp);

    return *result;
}

ClockingBlockSymbol::ClockingBlockSymbol(Compilation& compilation, std::string_view name,
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
                    auto& diag = scope.addDiag(diag::MultipleDefaultInputSkew,
                                               dir.inputSkew->sourceRange());
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
        SLANG_ASSERT(scope && syntax);

        ASTContext context(*scope, LookupLocation::before(*this));
        event = &EventListControl::fromSyntax(getCompilation(),
                                              *syntax->as<ClockingDeclarationSyntax>().event,
                                              context);
    }
    return *event;
}

ClockingSkew ClockingBlockSymbol::getDefaultInputSkew() const {
    if (!defaultInputSkew) {
        if (inputSkewSyntax) {
            auto scope = getParentScope();
            SLANG_ASSERT(scope);

            ASTContext context(*scope, LookupLocation::before(*this));
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
            SLANG_ASSERT(scope);

            ASTContext context(*scope, LookupLocation::before(*this));
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

RandSeqProductionSymbol::RandSeqProductionSymbol(Compilation& compilation, std::string_view name,
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
        SmallVector<const FormalArgumentSymbol*> args;
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

std::span<const RandSeqProductionSymbol::Rule> RandSeqProductionSymbol::getRules() const {
    if (!rules) {
        auto syntax = getSyntax();
        SLANG_ASSERT(syntax);

        ASTContext context(*this, LookupLocation::max);

        auto blocks = membersOfType<StatementBlockSymbol>();
        auto blockIt = blocks.begin();

        SmallVector<Rule, 8> buffer;
        for (auto rule : syntax->as<ProductionSyntax>().rules) {
            SLANG_ASSERT(blockIt != blocks.end());
            buffer.push_back(createRule(*rule, context, *blockIt++));
        }

        rules = buffer.copy(context.getCompilation());
    }
    return *rules;
}

const RandSeqProductionSymbol* RandSeqProductionSymbol::findProduction(std::string_view name,
                                                                       SourceRange nameRange,
                                                                       const ASTContext& context) {
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
    const RsProdItemSyntax& syntax, const ASTContext& context) {

    auto symbol = findProduction(syntax.name.valueText(), syntax.name.range(), context);
    if (!symbol)
        return ProdItem(nullptr, {});

    SmallVector<const Expression*> args;
    CallExpression::bindArgs(syntax.argList, symbol->arguments, symbol->name, syntax.sourceRange(),
                             context, args, /* isBuiltInMethod */ false);

    return ProdItem(symbol, args.copy(context.getCompilation()));
}

const RandSeqProductionSymbol::CaseProd& RandSeqProductionSymbol::createCaseProd(
    const RsCaseSyntax& syntax, const ASTContext& context) {

    SmallVector<const ExpressionSyntax*> expressions;
    SmallVector<ProdItem, 8> prods;
    std::optional<ProdItem> defItem;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardRsCaseItem: {
                auto& sci = item->as<StandardRsCaseItemSyntax>();
                auto pi = createProdItem(*sci.item, context);
                for (auto es : sci.expressions) {
                    expressions.push_back(es);
                    prods.push_back(pi);
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
                SLANG_UNREACHABLE;
        }
    }

    SmallVector<const Expression*> bound;
    Expression::bindMembershipExpressions(context, TokenKind::CaseKeyword,
                                          /* requireIntegral */ false,
                                          /* unwrapUnpacked */ false,
                                          /* allowTypeReferences */ true, /* allowOpenRange */ true,
                                          *syntax.expr, expressions, bound);

    SmallVector<CaseItem, 8> items;
    SmallVector<const Expression*> group;
    auto& comp = context.getCompilation();
    auto boundIt = bound.begin();
    auto prodIt = prods.begin();
    auto expr = *boundIt++;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardRsCaseItem: {
                auto& sci = item->as<StandardRsCaseItemSyntax>();
                for (size_t i = 0; i < sci.expressions.size(); i++)
                    group.push_back(*boundIt++);

                items.push_back({group.copy(comp), *prodIt++});
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
    const RsRuleSyntax& syntax, const ASTContext& context, const StatementBlockSymbol& ruleBlock) {

    auto blockRange = ruleBlock.membersOfType<StatementBlockSymbol>();
    auto blockIt = blockRange.begin();

    auto& comp = context.getCompilation();
    SmallVector<const ProdBase*> prods;
    for (auto p : syntax.prods) {
        switch (p->kind) {
            case SyntaxKind::RsProdItem:
                prods.push_back(
                    comp.emplace<ProdItem>(createProdItem(p->as<RsProdItemSyntax>(), context)));
                break;
            case SyntaxKind::RsCodeBlock: {
                SLANG_ASSERT(blockIt != blockRange.end());
                prods.push_back(comp.emplace<CodeBlockProd>(*blockIt++));
                break;
            }
            case SyntaxKind::RsIfElse: {
                auto& ries = p->as<RsIfElseSyntax>();
                auto& expr = Expression::bind(*ries.condition, context);
                auto ifItem = createProdItem(*ries.ifItem, context);

                std::optional<ProdItem> elseItem;
                if (ries.elseClause)
                    elseItem = createProdItem(*ries.elseClause->item, context);

                if (!expr.bad())
                    context.requireBooleanConvertible(expr);

                prods.push_back(comp.emplace<IfElseProd>(expr, ifItem, elseItem));
                break;
            }
            case SyntaxKind::RsRepeat: {
                auto& rrs = p->as<RsRepeatSyntax>();
                auto& expr = Expression::bind(*rrs.expr, context);
                auto item = createProdItem(*rrs.item, context);
                prods.push_back(comp.emplace<RepeatProd>(expr, item));

                context.requireIntegral(expr);
                break;
            }
            case SyntaxKind::RsCase:
                prods.push_back(&createCaseProd(p->as<RsCaseSyntax>(), context));
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    const Expression* weightExpr = nullptr;
    std::optional<CodeBlockProd> codeBlock;
    if (auto wc = syntax.weightClause) {
        weightExpr = &Expression::bind(*wc->weight, context);
        context.requireIntegral(*weightExpr);

        if (wc->codeBlock) {
            SLANG_ASSERT(blockIt != blockRange.end());
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

    for (auto& block : blockRange) {
        Statement::StatementContext stmtCtx(context);
        stmtCtx.flags = StatementFlags::InRandSeq;
        block.getStatement(context, stmtCtx);
    }

    return {ruleBlock, prods.copy(comp), weightExpr, randJoinExpr, codeBlock, isRandJoin};
}

void RandSeqProductionSymbol::createRuleVariables(const RsRuleSyntax& syntax, const Scope& scope,
                                                  SmallVectorBase<const Symbol*>& results) {
    SmallMap<const RandSeqProductionSymbol*, uint32_t, 8> prodMap;
    auto countProd = [&](const RsProdItemSyntax& item) {
        auto symbol = Lookup::unqualified(scope, item.name.valueText(),
                                          LookupFlags::AllowDeclaredAfter);
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
                            SLANG_UNREACHABLE;
                    }
                }
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    auto& comp = scope.getCompilation();
    for (auto [symbol, count] : prodMap) {
        auto var = comp.emplace<VariableSymbol>(symbol->name, syntax.getFirstToken().location(),
                                                VariableLifetime::Automatic);
        var->flags |= VariableFlags::Const | VariableFlags::CompilerGenerated;

        if (count == 1) {
            var->setType(symbol->getReturnType());
        }
        else {
            ConstantRange range{1, int32_t(count)};
            var->setType(
                FixedSizeUnpackedArrayType::fromDim(scope, symbol->getReturnType(), range, syntax));
        }

        results.push_back(var);
    }
}

void RandSeqProductionSymbol::serializeTo(ASTSerializer& serializer) const {
    auto writeItem = [&](std::string_view propName, const ProdItem& item) {
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
                    SLANG_UNREACHABLE;
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

AnonymousProgramSymbol::AnonymousProgramSymbol(Compilation& compilation, SourceLocation loc) :
    Symbol(SymbolKind::AnonymousProgram, "", loc), Scope(compilation, this) {
}

AnonymousProgramSymbol& AnonymousProgramSymbol::fromSyntax(Scope& scope,
                                                           const AnonymousProgramSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<AnonymousProgramSymbol>(comp, syntax.keyword.location());
    result->setSyntax(syntax);

    for (auto member : syntax.members)
        result->addMembers(*member);

    // All members also get hoisted into the parent scope.
    for (auto member = result->getFirstMember(); member; member = member->getNextSibling())
        scope.addMember(*comp.emplace<TransparentMemberSymbol>(*member));

    return *result;
}

NetAliasSymbol& NetAliasSymbol::fromSyntax(const ASTContext& parentContext,
                                           const syntax::NetAliasSyntax& syntax,
                                           SmallVectorBase<const Symbol*>& implicitNets) {
    SmallSet<std::string_view, 8> seenNames;
    ASTContext context = parentContext.resetFlags(ASTFlags::NonProcedural);
    auto& comp = context.getCompilation();
    auto& netType = context.scope->getDefaultNetType();

    for (auto expr : syntax.nets) {
        // If not explicitly disabled check for implicit nets.
        if (!netType.isError()) {
            SmallVector<const IdentifierNameSyntax*> implicitNetNames;
            Expression::findPotentiallyImplicitNets(*expr, context, implicitNetNames);

            for (auto ins : implicitNetNames) {
                if (seenNames.emplace(ins->identifier.valueText()).second)
                    implicitNets.push_back(&NetSymbol::createImplicit(comp, *ins, netType));
            }
        }
    }

    auto result = comp.emplace<NetAliasSymbol>(syntax.keyword.location());
    result->setSyntax(syntax);
    result->setAttributes(*context.scope, syntax.attributes);
    return *result;
}

struct NetAliasVisitor {
    const ASTContext& context;
    const NetType* commonNetType = nullptr;
    bool issuedError = false;

    NetAliasVisitor(const ASTContext& context) : context(context) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            switch (expr.kind) {
                case ExpressionKind::NamedValue:
                case ExpressionKind::MemberAccess:
                case ExpressionKind::ElementSelect:
                case ExpressionKind::RangeSelect: {
                    if (auto sym = expr.getSymbolReference()) {
                        if (sym->kind != SymbolKind::Net) {
                            context.addDiag(diag::NetAliasNotANet, expr.sourceRange) << sym->name;
                        }
                        else {
                            auto& nt = sym->template as<NetSymbol>().netType;
                            if (!commonNetType) {
                                commonNetType = &nt;
                            }
                            else if (commonNetType != &nt && !issuedError) {
                                auto& diag = context.addDiag(diag::NetAliasCommonNetType,
                                                             expr.sourceRange);
                                diag << sym->name;
                                diag << nt.name << commonNetType->name;
                                issuedError = true;
                            }
                        }
                    }
                    break;
                }
                case ExpressionKind::HierarchicalValue:
                    context.addDiag(diag::NetAliasHierarchical, expr.sourceRange);
                    break;
                default:
                    if constexpr (HasVisitExprs<T, NetAliasVisitor>)
                        expr.visitExprs(*this);
                    break;
            }
        }
    }
};

std::span<const Expression* const> NetAliasSymbol::getNetReferences() const {
    if (netRefs)
        return *netRefs;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    SLANG_ASSERT(scope && syntax);

    // TODO: there should be a global check somewhere that any given bit
    // of a net isn't aliased to the same target signal bit multiple times.
    bitwidth_t bitWidth = 0;
    bool issuedError = false;
    SmallVector<const Expression*> buffer;
    ASTContext context(*scope, LookupLocation::after(*this),
                       ASTFlags::NonProcedural | ASTFlags::NotADriver);
    NetAliasVisitor visitor(context);

    for (auto exprSyntax : syntax->as<NetAliasSyntax>().nets) {
        auto& netRef = Expression::bind(*exprSyntax, context);
        if (!netRef.requireLValue(context))
            continue;

        if (!bitWidth) {
            bitWidth = netRef.type->getBitWidth();
        }
        else if (bitWidth != netRef.type->getBitWidth() && !issuedError) {
            auto& diag = context.addDiag(diag::NetAliasWidthMismatch, netRef.sourceRange);
            diag << netRef.type->getBitWidth() << bitWidth;
            issuedError = true;
        }

        netRef.visit(visitor);
        buffer.push_back(&netRef);
    }

    netRefs = buffer.copy(scope->getCompilation());
    return *netRefs;
}

void NetAliasSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("netReferences");
    for (auto expr : getNetReferences())
        serializer.serialize(*expr);
    serializer.endArray();
}

} // namespace slang::ast
