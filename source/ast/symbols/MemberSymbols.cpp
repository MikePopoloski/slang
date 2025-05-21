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
#include "slang/ast/EvalContext.h"
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
#include "slang/util/PoolAllocator.h"
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
                                        SourceLocation errorLoc, bool isFromExport) {
    auto& comp = lookupScope.getCompilation();
    auto package = comp.getPackage(packageName);
    if (!package) {
        if (!packageName.empty() && !comp.hasFlag(CompilationFlags::LintMode))
            lookupScope.addDiag(diag::UnknownPackage, errorLoc) << packageName;
    }
    else {
        // Make sure we aren't trying to import/export our own package.
        auto currScope = &lookupScope;
        do {
            auto& sym = currScope->asSymbol();
            if (package == &sym) {
                if (isFromExport)
                    lookupScope.addDiag(diag::PackageExportSelf, errorLoc);
                else
                    lookupScope.addDiag(diag::PackageImportSelf, errorLoc);
                return nullptr;
            }

            currScope = sym.getParentScope();
        } while (currScope);
    }

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

        package_ = findPackage(packageName, *scope, loc, isFromExport);
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

        package = findPackage(packageName, *scope, loc, isFromExport);
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
    ValueSymbol(SymbolKind::ModportPort, name, loc), direction(direction) {
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
    if (direction != ArgumentDirection::In) {
        checkCtx.flags |= ASTFlags::LValue;
        if (direction == ArgumentDirection::InOut)
            checkCtx.flags |= ASTFlags::LAndRValue;
    }

    auto loc = result->location;
    auto& expr = ValueExpressionBase::fromSymbol(checkCtx, *result->internalSymbol, nullptr,
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

    bitmask<ASTFlags> extraFlags;
    if (direction == ArgumentDirection::Out || direction == ArgumentDirection::InOut) {
        extraFlags = ASTFlags::LValue;
        if (direction == ArgumentDirection::InOut)
            extraFlags |= ASTFlags::LAndRValue;
    }

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
                        if (subPort->previewNode)
                            modport->addMembers(*subPort->previewNode);

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
    EvalContext evalCtx(context);
    std::optional<std::string> str = FmtHelpers::formatDisplay(*context.scope, evalCtx, args);
    evalCtx.reportAllDiags();

    if (!str)
        return {};

    if (str->empty())
        return ""sv;

    str->insert(0, ": ");

    // Copy the string into permanent memory.
    auto mem = context.getCompilation().allocate(str->size(), alignof(char));
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

    auto syntax = expr.syntax;
    SLANG_ASSERT(syntax);
    while (syntax->kind == SyntaxKind::ParenthesizedExpression)
        syntax = syntax->as<ParenthesizedExpressionSyntax>().expression;

    auto opToken = syntax->as<BinaryExpressionSyntax>().operatorToken;

    auto lc = expr.left().constant;
    auto rc = expr.right().constant;
    SLANG_ASSERT(lc && rc);

    auto& note = result.addNote(diag::NoteComparisonReduces, opToken.location());
    note << expr.sourceRange;
    note << *lc << opToken.rawText() << *rc;
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

    if (scope->isUninstantiated())
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
    ValueSymbol(SymbolKind::PrimitivePort, name, loc), direction(direction) {
    // All primitive ports are single bit logic types.
    setType(compilation.getLogicType());
}

void PrimitivePortSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("direction", toString(direction));
}

// A trie node used to detect duplicate primitive rows.
// Each 'bit' is one input value in the row.
class BitTrie {
public:
    // Determines whether the trie contains at least one row that
    // matches the given inputs (and possibly state char).
    bool contains(std::span<const char> inputs, char stateChar) const {
        auto handle = [](const BitTrie& node, SmallVector<const BitTrie*>& nextNodes, int index,
                         bool) {
            if (node.children[index])
                nextNodes.push_back(node.children[index]);
        };

        SmallVector<const BitTrie*> nodes;
        nodes.push_back(this);
        traverse(nodes, inputs, stateChar, handle);

        return std::ranges::any_of(nodes, [](auto node) { return node->entry != nullptr; });
    }

    // Inserts the given row into the trie. The provided results vector will
    // be filled with all existing rows that match the new one we're inserting.
    template<typename TAllocator>
    void insert(const UdpEntrySyntax& syntax, std::span<const char> inputs, char stateChar,
                TAllocator& allocator, SmallVector<const UdpEntrySyntax*>& results) {
        BitTrie* primaryNode = this;
        auto handle = [&primaryNode, &allocator](const BitTrie& constNode,
                                                 SmallVector<BitTrie*>& nextNodes, int index,
                                                 bool primary) {
            // If we are handling a primary and the current node is also
            // the primary node we should allocate if missing, otherwise
            // we only add if it already exists.
            BitTrie& node = const_cast<BitTrie&>(constNode);
            if (primary && primaryNode == &node) {
                if (!node.children[index])
                    node.children[index] = allocator.emplace();
                primaryNode = node.children[index];
            }

            if (node.children[index])
                nextNodes.push_back(node.children[index]);
        };

        SmallVector<BitTrie*> nodes;
        nodes.push_back(this);
        traverse(nodes, inputs, stateChar, handle);

        for (auto node : nodes) {
            if (node->entry)
                results.push_back(node->entry);
        }

        // Store the provided row so as not to miss info in case of possible overlap.
        // If the primary->entry already has a value, then rewriting will not spoil
        // anything, since the rewriting will be to the equivalent grammar.
        primaryNode->entry = &syntax;
    }

private:
    // Walks the provided input string (and optional state char) and invokes the
    // given callback on all relevant nodes.
    template<typename TNode, typename TCallback>
    void traverse(SmallVector<TNode*>& nodes, std::span<const char> inputs, char stateChar,
                  TCallback&& callback) const {
        auto advance = [&](char c) {
            SmallVector<TNode*> nextNodes;
            for (auto node : nodes)
                node->nextNodesFor(c, nextNodes, callback);
            nodes = std::move(nextNodes);
        };

        for (char c : inputs) {
            // Skip the closing paren, since it doesn't add
            // any additional signal to the bitstring.
            if (c == ')')
                continue;

            // Advance along the path.
            advance(c);

            // Check if we need special handling for this character.
            switch (c) {
                case '*':
                    advance('?');
                    advance('?');
                    break;
                case 'r':
                    advance('0');
                    advance('1');
                    break;
                case 'f':
                    advance('1');
                    advance('0');
                    break;
                case 'p':
                    advance('6');
                    advance('7');
                    break;
                case 'n':
                    advance('7');
                    advance('6');
                    break;
                default:
                    break;
            }
        }

        // Include the state field if present.
        if (stateChar)
            advance(stateChar);
    }

    // Maps the given character to one or more of our child indices,
    // invoking the provided callback for each one.
    template<typename TNode, typename TCallback>
    void nextNodesFor(char c, SmallVector<TNode*>& nextNodes, TCallback&& callback) const {
        // Map the character to one or more of our child entries.
        // The "primary" entry is the one that directly matches the
        // character, and there can be several secondary entries that
        // can match based on wildcard values.
        auto handle = [&](int index, bool primary = false) {
            callback(*this, nextNodes, index, primary);
        };

        switch (c) {
            case '0':
                handle(0, true);
                handle(3);
                handle(4);
                handle(6);
                break;
            case '1':
                handle(1, true);
                handle(3);
                handle(4);
                handle(7);
                break;
            case 'x':
                handle(2, true);
                handle(3);
                handle(6);
                handle(7);
                break;
            case '?':
                handle(3, true);
                handle(0);
                handle(1);
                handle(2);
                handle(4);
                handle(6);
                handle(7);
                break;
            case 'b':
                handle(4, true);
                handle(0);
                handle(1);
                handle(3);
                break;
            case '(':
            case '*':
            case 'r':
            case 'f':
            case 'p':
            case 'n':
                handle(5, true);
                break;
            // Below are implicit node identifiers that cannot be found in the UDP grammar. They are
            // helpers for `p` and `n`.
            case '6':
                // Handling `0` or `x`.
                handle(6, true);
                handle(0);
                handle(2);
                handle(3);
                break;
            case '7':
                // Handling `1` or `x` (for `p` and `n` matching cases).
                handle(7, true);
                handle(1);
                handle(2);
                handle(3);
                break;
            default:
                // On error clear all nodes. Assume someone else
                // (the parser) has reported the error already.
                nextNodes.clear();
                break;
        }
    }

    BitTrie* children[8] = {};
    const UdpEntrySyntax* entry = nullptr;
};

static void createTableRow(const Scope& scope, const UdpEntrySyntax& syntax,
                           SmallVector<PrimitiveSymbol::TableEntry>& table, size_t numPorts,
                           BitTrie& trie, PoolAllocator<BitTrie>& trieAlloc) {
    // Normalize all of the inputs into a single string.
    SmallVector<char> inputs;
    size_t numInputs = 0;
    bool allX = true;
    bool isEdgeSensitive = false;
    for (auto input : syntax.inputs) {
        if (input->kind == SyntaxKind::UdpEdgeField) {
            isEdgeSensitive = true;
            auto& edge = input->as<UdpEdgeFieldSyntax>();
            inputs.push_back('(');

            SmallVector<char> buf;
            for (char c : edge.first.rawText())
                buf.push_back(charToLower(c));
            for (char c : edge.second.rawText())
                buf.push_back(charToLower(c));

            if (buf.size() != 2)
                return;

            // Special case for (x?) and (?x) -- pretend these were
            // written as (xb) and (bx), otherwise they're guaranteed
            // to error about the overlap between ? and the 'x' value.
            if (buf[0] == 'x' && buf[1] == '?') {
                inputs.push_back('x');
                inputs.push_back('b');
                allX = false;
            }
            else if (buf[0] == '?' && buf[1] == 'x') {
                inputs.push_back('b');
                inputs.push_back('x');
                allX = false;
            }
            else {
                inputs.push_back(buf[0]);
                inputs.push_back(buf[1]);
                allX &= buf[0] == 'x';
                allX &= buf[1] == 'x';
            }

            inputs.push_back(')');
            numInputs++;
        }
        else {
            auto tok = input->as<UdpSimpleFieldSyntax>().field;
            for (auto c : tok.rawText()) {
                auto d = charToLower(c);
                switch (d) {
                    case '*':
                    case 'r':
                    case 'f':
                    case 'p':
                    case 'n':
                        isEdgeSensitive = true;
                        break;
                    default:
                        break;
                }

                inputs.push_back(d);
                numInputs++;
                allX &= d == 'x';
            }
        }
    }

    if (numPorts >= 2 && numInputs != numPorts - 1) {
        auto& diag = scope.addDiag(diag::UdpWrongInputCount, syntax.inputs.sourceRange());
        diag << numInputs;
        diag << numPorts - 1;
        return;
    }

    auto getStateChar = [](const UdpFieldBaseSyntax* base) -> char {
        if (base && base->kind == SyntaxKind::UdpSimpleField) {
            auto raw = base->as<UdpSimpleFieldSyntax>().field.rawText();
            if (raw.size() == 1) {
                auto c = charToLower(raw[0]);
                switch (c) {
                    case '0':
                    case '1':
                    case 'x':
                    case '?':
                    case 'b':
                        return c;
                    default:
                        break;
                }
            }
        }
        return 0;
    };

    char stateChar = 0;
    if (syntax.current) {
        stateChar = getStateChar(syntax.current);
        if (!stateChar)
            return;
    }

    auto getOutputChar = [](const UdpFieldBaseSyntax* base) -> char {
        if (base && base->kind == SyntaxKind::UdpSimpleField) {
            auto raw = base->as<UdpSimpleFieldSyntax>().field.rawText();
            if (raw.size() == 1) {
                auto c = charToLower(raw[0]);
                switch (c) {
                    case '-':
                    case '0':
                    case '1':
                    case 'x':
                        return c;
                    default:
                        break;
                }
            }
        }
        return 0;
    };

    auto outputChar = getOutputChar(syntax.next);
    if (!outputChar)
        return;

    auto matchOutput = [](char state1, char output1, char output2) -> bool {
        if (output1 != '-')
            return false;

        switch (state1) {
            case '0':
            case '1':
            case 'x':
                return output2 == state1;
            case 'b':
                return output2 == '0' || output2 == '1';
            case '?':
                return output2 == '0' || output2 == '1' || output2 == 'x';
            default:
                // Can happen if e.g. the UDP doesn't have a state char (combinational).
                return false;
        }
    };

    SmallVector<const UdpEntrySyntax*> conflicts;
    trie.insert(syntax, inputs, stateChar, trieAlloc, conflicts);
    if (!conflicts.empty()) {
        for (const auto* existing : conflicts) {
            // This is an error if the existing row has a different output,
            // otherwise it's just silently ignored.
            auto existingOutput = getOutputChar(existing->next);
            auto existingState = getStateChar(existing->current);
            if (existingOutput != outputChar &&
                !matchOutput(existingState, existingOutput, outputChar) &&
                !matchOutput(stateChar, outputChar, existingOutput)) {
                auto& diag = scope.addDiag(diag::UdpDupDiffOutput, syntax.sourceRange());
                diag.addNote(diag::NotePreviousDefinition, existing->sourceRange());
                return;
            }
        }
    }
    else if (allX && outputChar != 'x') {
        scope.addDiag(diag::UdpAllX, syntax.sourceRange());
        return;
    }

    auto inputSpan = inputs.copy(scope.getCompilation());
    table.push_back({std::string_view(inputSpan.data(), inputSpan.size()), stateChar, outputChar,
                     isEdgeSensitive});
}

const static std::vector<std::string_view> AllPrimEdges = {"(01)", "(0x)", "(10)",
                                                           "(1x)", "(x0)", "(x1)"};

static void checkPrimitiveEdgeCombinations(const PrimitiveSymbol& prim, const Scope& scope,
                                           const BitTrie& trie) {
    // Check that if the behavior of the UDP is sensitive to edges of any input, the desired
    // output state shall be specified for all edges of all inputs.
    if (!prim.isEdgeSensitive || prim.table.empty())
        return;

    SLANG_ASSERT(prim.ports.size() >= 2);
    auto numInputs = prim.ports.size() - 1;

    // Initial state is (01)000...
    std::string state(AllPrimEdges[0]);
    state.append(numInputs - 1, '0');

    // End state is xxx...(x1)
    std::string endState(numInputs - 1, 'x');
    endState.append("(x1)"sv);

    // Try to find the missing combinations by completely enumerating all
    // possible table rows.
    std::string noteStr;
    uint32_t noteCount = 0;
    Diagnostic* diag = nullptr;
    auto& comp = scope.getCompilation();

    while (true) {
        // Try to find the desired row in the trie we built earlier.
        if (!trie.contains(state, '?')) {
            // Not found, so we'll issue a warning if we don't have one already.
            if (!diag)
                diag = &scope.addDiag(diag::UdpCoverage, prim.location);

            if (noteCount >= comp.getOptions().maxUDPCoverageNotes) {
                noteStr += "...and more\n";
                break;
            }

            bool nextSplit = true;
            for (auto c : state) {
                if (c == '(')
                    nextSplit = false;
                else if (c == ')')
                    nextSplit = true;

                noteStr += c;
                if (nextSplit)
                    noteStr += ' ';
            }
            noteCount++;
            noteStr += '\n';
        }

        if (state.back() == ')' && state == endState)
            break;

        // Iterate state by increasing leftoutermost inputs.
        // For simple inputs value '0' goes to '1' and value '1' goes to `x`.
        // For edge inputs circular iteration occurs over 'AllPrimEdges' list.
        for (size_t i = 0; i < state.size(); ++i) {
            if (state[i] == '(') {
                std::string_view currEdge(&state[i], 4);
                if (currEdge == AllPrimEdges.back()) {
                    // We finished cycling this edge.
                    if (state.back() != 'x') {
                        state.replace(i, 4, AllPrimEdges[0]);
                        i += 3;
                        continue;
                    }

                    // Move edge input to the next position and set all others as '0'
                    std::ranges::fill(state, '0');
                    state.replace(i + 1, 4, AllPrimEdges[0]);
                    break;
                }

                auto it = std::find(AllPrimEdges.begin(), AllPrimEdges.end(), currEdge) + 1;
                state.replace(i, 4, *it);
                break;
            }

            if (state[i] == '0') {
                state[i] = '1';
                break;
            }

            if (state[i] == '1') {
                state[i] = 'x';
                break;
            }

            state[i] = '0';
        }
    }

    if (diag && !noteStr.empty()) {
        noteStr.pop_back();
        diag->addNote(diag::NoteUdpCoverage, SourceLocation::NoLocation) << noteStr;
    }
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
        auto externPrim = comp.getExternDefinition(primName, scope);
        if (!externPrim || externPrim->kind != SyntaxKind::ExternUdpDecl)
            scope.addDiag(diag::MissingExternWildcardPorts, portList->sourceRange()) << primName;
        else
            portList = externPrim->as<ExternUdpDeclSyntax>().portList;
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
                auto name = outputDecl.name;
                if (auto it = portMap.find(name.valueText()); it != portMap.end()) {
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
                    checkDup(port, name);

                    port->direction = PrimitivePortDirection::Out;
                    if (outputDecl.reg)
                        port->direction = PrimitivePortDirection::OutReg;

                    port->location = name.location();
                    port->setSyntax(outputDecl);
                    port->setAttributes(scope, decl->attributes);
                }
                else if (!name.valueText().empty()) {
                    auto& diag = scope.addDiag(diag::PrimitivePortUnknown, name.range());
                    diag << name.valueText();
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
                    else if (!name.valueText().empty()) {
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
            if (!port->getSyntax() && !port->name.empty()) {
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

    prim->ports = ports.copy(comp);
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

        BitTrie trie;
        BumpAllocator alloc;
        PoolAllocator<BitTrie> trieAlloc(alloc);
        SmallVector<TableEntry> table;
        for (auto entry : syntax.body->entries) {
            createTableRow(scope, *entry, table, ports.size(), trie, trieAlloc);
            if (!table.empty() && !prim->isEdgeSensitive)
                prim->isEdgeSensitive = table.back().isEdgeSensitive;
        }

        prim->table = table.copy(comp);
        checkPrimitiveEdgeCombinations(*prim, scope, trie);
    }

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
            serializer.write("inputs", row.inputs);
            if (row.state)
                serializer.write("state", std::string_view(&row.state, 1));
            serializer.write("output", std::string_view(&row.output, 1));
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
        if (item->previewNode)
            scope.addMembers(*item->previewNode);

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
    Symbol(SymbolKind::Sequence, name, loc), Scope(compilation, this) {
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
    Symbol(SymbolKind::Property, name, loc), Scope(compilation, this) {
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
    Symbol(SymbolKind::LetDecl, name, loc), Scope(compilation, this), exprSyntax(&exprSyntax) {
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
            if (item->previewNode)
                result->addMembers(*item->previewNode);

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
    Symbol(SymbolKind::ClockingBlock, name, loc), Scope(compilation, this) {
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
    Symbol(SymbolKind::RandSeqProduction, name, loc), Scope(compilation, this),
    declaredReturnType(*this) {
}

RandSeqProductionSymbol& RandSeqProductionSymbol::fromSyntax(const Scope& scope,
                                                             const ProductionSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<RandSeqProductionSymbol>(comp, syntax.name.valueText(),
                                                        syntax.name.location());
    result->setSyntax(syntax);

    if (syntax.dataType)
        result->declaredReturnType.setTypeSyntax(*syntax.dataType);
    else
        result->declaredReturnType.setType(comp.getVoidType());

    if (syntax.portList) {
        SmallVector<const FormalArgumentSymbol*> args;
        SubroutineSymbol::buildArguments(*result, scope, *syntax.portList,
                                         VariableLifetime::Automatic, args);
        result->arguments = args.copy(comp);
    }

    for (auto rule : syntax.rules) {
        if (rule->previewNode)
            result->addMembers(*rule->previewNode);

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
                                          /* allowTypeReferences */ true,
                                          /* allowValueRange */ true, *syntax.expr, expressions,
                                          bound);

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

struct NetAlias {
    not_null<const ValueSymbol*> sym;
    not_null<const Expression*> expr;
    DriverBitRange bounds;
};

struct NetAliasVisitor {
    const ASTContext& context;
    const NetType* commonNetType = nullptr;
    SmallVector<NetAlias> netAliases;
    EvalContext& evalCtx;
    bool issuedError = false;

    NetAliasVisitor(const ASTContext& context, EvalContext& evalCtx) :
        context(context), evalCtx(evalCtx) {}

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
                            auto& netSym = sym->template as<NetSymbol>();
                            if (auto bounds = ValueDriver::getBounds(expr, evalCtx,
                                                                     netSym.getType())) {
                                netAliases.push_back({&netSym, &expr, *bounds});
                            }

                            auto& nt = netSym.netType;
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

    SmallVector<const Expression*> buffer;
    ASTContext context(*scope, LookupLocation::after(*this),
                       ASTFlags::NonProcedural | ASTFlags::NotADriver);
    EvalContext evalCtx(context);
    NetAliasVisitor visitor(context, evalCtx);
    SmallVector<SmallVector<NetAlias>> netAliases;
    bitwidth_t bitWidth = 0;
    bool issuedError = false;

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
        if (!visitor.netAliases.empty()) {
            netAliases.emplace_back(std::move(visitor.netAliases));
            visitor.netAliases.clear();
        }
    }

    netRefs = buffer.copy(scope->getCompilation());
    if (issuedError || netAliases.empty())
        return *netRefs;

    // Compare every net alias expression to every other, finding the set of
    // bits that overlap and adding drivers for them so that we can catch
    // and report on duplicate and/or self aliases.
    auto& comp = scope->getCompilation();
    const size_t numAliases = netAliases.size();
    for (size_t i = 0; i < numAliases - 1; i++) {
        for (size_t j = i + 1; j < numAliases; j++) {
            auto& first = netAliases[i];
            auto& second = netAliases[j];
            auto firstIt = first.begin();
            auto firstEnd = first.end();
            auto secondIt = second.begin();
            auto secondEnd = second.end();

            // Compare each net reference or selection from the left hand side
            // to the corresponding elements on the right hand side. The individual
            // elements can differ in width, so consume bits from the larger side
            // and only advance when a side has been consumed.
            std::optional<std::pair<DriverBitRange, bool>> remainder;
            while (firstIt != firstEnd && secondIt != secondEnd) {
                auto& firstAlias = *firstIt;
                auto& secondAlias = *secondIt;
                auto firstRange = firstAlias.bounds;
                auto secondRange = secondAlias.bounds;

                if (remainder) {
                    if (remainder->second)
                        firstRange = remainder->first;
                    else
                        secondRange = remainder->first;
                    remainder.reset();
                }

                auto firstWidth = firstRange.second - firstRange.first + 1;
                auto secondWidth = secondRange.second - secondRange.first + 1;

                uint64_t width;
                if (firstWidth < secondWidth) {
                    width = firstWidth;
                    remainder = std::pair(
                        DriverBitRange(secondRange.first, secondRange.second - width), false);
                    firstIt++;
                }
                else {
                    width = secondWidth;
                    secondIt++;

                    if (firstWidth == secondWidth)
                        firstIt++;
                    else {
                        remainder = std::pair(
                            DriverBitRange(firstRange.first, firstRange.second - width), true);
                    }
                }

                comp.noteNetAlias(*scope, *firstAlias.sym,
                                  {firstRange.second - width + 1, firstRange.second},
                                  *firstAlias.expr, *secondAlias.sym,
                                  {secondRange.second - width + 1, secondRange.second},
                                  *secondAlias.expr);
            }
        }
    }

    return *netRefs;
}

void NetAliasSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("netReferences");
    for (auto expr : getNetReferences())
        serializer.serialize(*expr);
    serializer.endArray();
}

} // namespace slang::ast
