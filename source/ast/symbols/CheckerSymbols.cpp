//------------------------------------------------------------------------------
// CheckerSymbols.cpp
// Contains checker-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/CheckerSymbols.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace slang::parsing;
using namespace slang::syntax;

static bool isEmptyType(const DataTypeSyntax& syntax) {
    if (syntax.kind != SyntaxKind::ImplicitType)
        return false;

    auto& implicit = syntax.as<ImplicitTypeSyntax>();
    return !implicit.signing && implicit.dimensions.empty();
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

namespace {

using DimIterator = std::span<VariableDimensionSyntax*>::iterator;

Symbol* recurseCheckerArray(Compilation& comp, const CheckerSymbol& checker,
                            const HierarchicalInstanceSyntax& instance, const ASTContext& context,
                            DimIterator it, DimIterator end,
                            std::span<const AttributeInstanceSyntax* const> attributes,
                            SmallVectorBase<uint32_t>& path, bool isProcedural,
                            bitmask<InstanceFlags> flags) {
    if (it == end) {
        return &CheckerInstanceSymbol::fromSyntax(comp, context, checker, instance, attributes,
                                                  path, isProcedural, flags);
    }

    SLANG_ASSERT(instance.decl);
    auto nameToken = instance.decl->name;
    auto& dimSyntax = **it;
    ++it;

    // Evaluate the dimensions of the array. If this fails for some reason,
    // make up an empty array so that we don't get further errors when
    // things try to reference this symbol.
    auto dim = context.evalDimension(dimSyntax, /* requireRange */ true, /* isPacked */ false);
    if (!dim.isRange())
        return &InstanceArraySymbol::createEmpty(comp, nameToken.valueText(), nameToken.location());

    ConstantRange range = dim.range;
    if (range.width() > comp.getOptions().maxInstanceArray) {
        auto& diag = context.addDiag(diag::MaxInstanceArrayExceeded, dimSyntax.sourceRange());
        diag << "checker"sv << comp.getOptions().maxInstanceArray;
        return &InstanceArraySymbol::createEmpty(comp, nameToken.valueText(), nameToken.location());
    }

    SmallVector<const Symbol*> elements;
    for (uint32_t i = 0; i < range.width(); i++) {
        path.push_back(i);
        auto symbol = recurseCheckerArray(comp, checker, instance, context, it, end, attributes,
                                          path, isProcedural, flags);
        path.pop_back();

        symbol->name = "";
        elements.push_back(symbol);
    }

    auto result = comp.emplace<InstanceArraySymbol>(comp, nameToken.valueText(),
                                                    nameToken.location(), elements.copy(comp),
                                                    range);
    for (auto element : elements)
        result->addMember(*element);

    return result;
}

template<typename TSyntax>
void createCheckers(const CheckerSymbol& checker, const TSyntax& syntax, const ASTContext& context,
                    SmallVectorBase<const Symbol*>& results,
                    SmallVectorBase<const Symbol*>& implicitNets, bool isProcedural,
                    bitmask<InstanceFlags> flags) {
    if (syntax.parameters)
        context.addDiag(diag::CheckerParameterAssign, syntax.parameters->sourceRange());

    SmallSet<std::string_view, 8> implicitNetNames;
    SmallVector<uint32_t> path;

    auto& comp = context.getCompilation();
    auto& netType = context.scope->getDefaultNetType();

    for (auto instance : syntax.instances) {
        path.clear();

        if (!isProcedural) {
            detail::createImplicitNets(*instance, context, netType, flags, implicitNetNames,
                                       implicitNets);
        }

        if (!instance->decl) {
            context.addDiag(diag::InstanceNameRequired, instance->sourceRange());
            results.push_back(&CheckerInstanceSymbol::fromSyntax(
                comp, context, checker, *instance, syntax.attributes, path, isProcedural, flags));
        }
        else {
            auto dims = instance->decl->dimensions;
            auto symbol = recurseCheckerArray(comp, checker, *instance, context, dims.begin(),
                                              dims.end(), syntax.attributes, path, isProcedural,
                                              flags);
            results.push_back(symbol);
        }
    }
}

} // namespace

CheckerInstanceSymbol::CheckerInstanceSymbol(std::string_view name, SourceLocation loc,
                                             CheckerInstanceBodySymbol& body) :
    InstanceSymbolBase(SymbolKind::CheckerInstance, name, loc), body(body) {
    body.parentInstance = this;
}

void CheckerInstanceSymbol::fromSyntax(const CheckerSymbol& checker,
                                       const HierarchyInstantiationSyntax& syntax,
                                       const ASTContext& context,
                                       SmallVectorBase<const Symbol*>& results,
                                       SmallVectorBase<const Symbol*>& implicitNets,
                                       bitmask<InstanceFlags> flags) {
    createCheckers(checker, syntax, context, results, implicitNets,
                   /* isProcedural */ false, flags);
}

void CheckerInstanceSymbol::fromSyntax(const CheckerInstantiationSyntax& syntax,
                                       const ASTContext& context,
                                       SmallVectorBase<const Symbol*>& results,
                                       SmallVectorBase<const Symbol*>& implicitNets,
                                       bitmask<InstanceFlags> flags) {
    // If this instance is not instantiated then we'll just fill in a placeholder
    // and move on. This is likely inside an untaken generate branch.
    if (context.scope->isUninstantiated()) {
        UninstantiatedDefSymbol::fromSyntax(context.getCompilation(), syntax, context, results,
                                            implicitNets);
        return;
    }

    auto& comp = context.getCompilation();
    auto& typeExpr = ArbitrarySymbolExpression::fromSyntax(comp, *syntax.type, context);
    if (typeExpr.bad())
        return;

    auto symbol = typeExpr.getSymbolReference();
    SLANG_ASSERT(symbol);

    if (symbol->kind != SymbolKind::Checker) {
        if (symbol->kind == SymbolKind::ClassType) {
            context.addDiag(diag::CheckerClassBadInstantiation, syntax.sourceRange())
                << symbol->name;
        }
        else if (symbol->kind == SymbolKind::Subroutine) {
            context.addDiag(diag::CheckerFuncBadInstantiation, syntax.sourceRange())
                << symbol->name;
        }
        else {
            auto& diag = context.addDiag(diag::NotAChecker, syntax.sourceRange());
            diag << symbol->name << symbol->name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
        }
        return;
    }

    // Only procedural if declared via a statement.
    const bool isProcedural = syntax.parent &&
                              syntax.parent->kind == SyntaxKind::CheckerInstanceStatement;

    createCheckers(symbol->as<CheckerSymbol>(), syntax, context, results, implicitNets,
                   isProcedural, flags);
}

static const Symbol* createCheckerFormal(Compilation& comp, const AssertionPortSymbol& port,
                                         CheckerInstanceBodySymbol& instance,
                                         const ExpressionSyntax*& outputInitialSyntax,
                                         const ASTContext& context) {
    if (auto portSyntax = port.getSyntax(); portSyntax && portSyntax->previewNode)
        instance.addMembers(*portSyntax->previewNode);

    // Output ports are special; they aren't involved in the rewriting process,
    // they just act like normal formal ports / arguments.
    if (port.direction == ArgumentDirection::Out) {
        auto arg = comp.emplace<FormalArgumentSymbol>(port.name, port.location, *port.direction,
                                                      VariableLifetime::Static);
        arg->getDeclaredType()->setLink(port.declaredType);

        if (auto portSyntax = port.getSyntax()) {
            arg->setSyntax(*portSyntax);
            arg->setAttributes(instance, portSyntax->as<AssertionItemPortSyntax>().attributes);
        }

        if (port.defaultValueSyntax)
            outputInitialSyntax = context.requireSimpleExpr(*port.defaultValueSyntax);

        instance.addMember(*arg);
        return arg;
    }
    else {
        // Clone all of the formal arguments and add them to the instance so that
        // members in the body can reference them.
        auto& cloned = port.clone(instance);
        instance.addMember(cloned);
        return &cloned;
    }
}

CheckerInstanceSymbol& CheckerInstanceSymbol::fromSyntax(
    Compilation& comp, const ASTContext& parentContext, const CheckerSymbol& checker,
    const HierarchicalInstanceSyntax& syntax,
    std::span<const AttributeInstanceSyntax* const> attributes, SmallVectorBase<uint32_t>& path,
    bool isProcedural, bitmask<InstanceFlags> flags) {

    ASTContext context = parentContext;
    auto parentSym = context.tryFillAssertionDetails();
    auto [name, loc] = detail::getNameLoc(syntax);

    uint32_t depth = 0;
    if (parentSym) {
        if (parentSym->kind == SymbolKind::CheckerInstanceBody) {
            auto& checkerBody = parentSym->as<CheckerInstanceBodySymbol>();
            depth = checkerBody.instanceDepth + 1;
            if (depth > comp.getOptions().maxCheckerInstanceDepth) {
                auto& diag = context.addDiag(diag::MaxInstanceDepthExceeded, loc);
                diag << "checker"sv;
                diag << comp.getOptions().maxCheckerInstanceDepth;
                return createInvalid(checker, depth);
            }

            if (checkerBody.flags.has(InstanceFlags::ParentFromBind))
                flags |= InstanceFlags::ParentFromBind;
        }
        else if (parentSym->as<InstanceBodySymbol>().flags.has(InstanceFlags::ParentFromBind)) {
            flags |= InstanceFlags::ParentFromBind;
        }
    }

    if (flags.has(InstanceFlags::FromBind)) {
        if (flags.has(InstanceFlags::ParentFromBind)) {
            context.addDiag(diag::BindUnderBind, syntax.sourceRange());
            return createInvalid(checker, depth);
        }

        // If our parent is from a bind statement, pass down the flag
        // so that we prevent further binds below us too.
        flags |= InstanceFlags::ParentFromBind;
        context.flags |= ASTFlags::BindInstantiation;
    }

    // It's illegal to instantiate checkers inside the procedures of other checkers.
    if (parentSym && parentSym->kind == SymbolKind::CheckerInstanceBody && isProcedural)
        context.addDiag(diag::CheckerInCheckerProc, syntax.sourceRange());

    auto assertionDetails = comp.allocAssertionDetails();
    auto body = comp.emplace<CheckerInstanceBodySymbol>(comp, checker, *assertionDetails,
                                                        parentContext, depth, isProcedural, flags);

    auto checkerSyntax = checker.getSyntax();
    SLANG_ASSERT(checkerSyntax);
    body->setSyntax(*checkerSyntax);

    assertionDetails->symbol = &checker;
    assertionDetails->instanceLoc = loc;

    // Build port connection map from formals to connection expressions.
    SmallVector<Connection> connections;
    size_t orderedIndex = 0;
    PortConnection::ConnMap connMap(syntax.connections, *context.scope, context.getLocation());
    for (auto port : checker.ports) {
        if (port->name.empty())
            continue;

        const ExpressionSyntax* outputInitialSyntax = nullptr;
        auto actualArg = createCheckerFormal(comp, *port, *body, outputInitialSyntax, context);

        const ASTContext* argCtx = &context;
        const PropertyExprSyntax* expr = nullptr;
        std::optional<ASTContext> defValCtx;
        std::span<const AttributeSymbol* const> attrs;

        auto setDefault = [&](std::optional<DeferredSourceRange> explicitRange) {
            if (!port->defaultValueSyntax || port->direction != ArgumentDirection::In) {
                auto code = explicitRange ? diag::CheckerArgCannotBeEmpty : diag::UnconnectedArg;
                auto& diag = context.addDiag(code, explicitRange ? explicitRange->get()
                                                                 : syntax.sourceRange());
                diag << port->name;
            }
            else {
                expr = port->defaultValueSyntax;
                defValCtx.emplace(checker, LookupLocation::after(*port));
                defValCtx->assertionInstance = assertionDetails;
                defValCtx->flags |= ASTFlags::AssertionDefaultArg;
                argCtx = &defValCtx.value();
            }
        };

        auto createImplicitNamed = [&](DeferredSourceRange range,
                                       bool isWildcard) -> const PropertyExprSyntax* {
            bitmask<LookupFlags> lf;
            if (isWildcard)
                lf |= LookupFlags::DisallowWildcardImport;

            if (flags.has(InstanceFlags::FromBind))
                lf |= LookupFlags::DisallowWildcardImport | LookupFlags::DisallowUnitReferences;

            auto symbol = Lookup::unqualified(*context.scope, port->name, lf);
            if (!symbol) {
                // If this is a wildcard connection, we're allowed to use the port's default value,
                // if it has one.
                if (isWildcard && port->defaultValueSyntax &&
                    port->direction == ArgumentDirection::In) {
                    return port->defaultValueSyntax;
                }

                context.addDiag(diag::ImplicitNamedPortNotFound, range.get()) << port->name;
                return nullptr;
            }

            // Create an expression tree that can stand in for this reference.
            auto nameSyntax = comp.emplace<IdentifierNameSyntax>(
                Token(comp, TokenKind::Identifier, {}, port->name, range.get().start()));
            auto seqSyntax = comp.emplace<SimpleSequenceExprSyntax>(*nameSyntax, nullptr);
            return comp.emplace<SimplePropertyExprSyntax>(*seqSyntax);
        };

        if (connMap.usingOrdered) {
            if (orderedIndex >= connMap.orderedConns.size()) {
                orderedIndex++;
                setDefault({});
            }
            else {
                const PortConnectionSyntax& pc = *connMap.orderedConns[orderedIndex++];
                attrs = AttributeSymbol::fromSyntax(pc.attributes, *context.scope,
                                                    context.getLocation());

                if (pc.kind == SyntaxKind::OrderedPortConnection)
                    expr = pc.as<OrderedPortConnectionSyntax>().expr;
                else
                    setDefault(pc);
            }
        }
        else {
            auto it = connMap.namedConns.find(port->name);
            if (it == connMap.namedConns.end()) {
                if (connMap.hasWildcard)
                    expr = createImplicitNamed(connMap.wildcardRange, true);
                else
                    setDefault({});
            }
            else {
                // We have a named connection; there are two possibilities here:
                // - An explicit connection (with an optional expression)
                // - An implicit connection, where we have to look up the name ourselves
                const NamedPortConnectionSyntax& conn = *it->second.first;
                it->second.second = true;

                attrs = AttributeSymbol::fromSyntax(conn.attributes, *context.scope,
                                                    context.getLocation());
                if (conn.openParen) {
                    // For explicit named port connections, having an empty expression means no
                    // connection, so we never take the default value here.
                    expr = conn.expr;
                    if (!expr) {
                        auto& diag = context.addDiag(diag::CheckerArgCannotBeEmpty,
                                                     conn.sourceRange());
                        diag << port->name;
                    }
                }
                else {
                    expr = createImplicitNamed(conn.name.range(), false);
                }
            }
        }

        assertionDetails->argumentMap.emplace(actualArg, std::make_tuple(expr, *argCtx));
        connections.emplace_back(*body, *actualArg, outputInitialSyntax, attrs);
    }

    if (connMap.usingOrdered) {
        if (orderedIndex < connMap.orderedConns.size()) {
            auto connLoc = connMap.orderedConns[orderedIndex]->getFirstToken().location();
            auto& diag = context.addDiag(diag::TooManyPortConnections, connLoc);
            diag << checker.name;
            diag << connMap.orderedConns.size();
            diag << orderedIndex;
        }
    }
    else {
        for (auto& pair : connMap.namedConns) {
            // We marked all the connections that we used, so anything left over is a connection
            // for a non-existent port.
            if (!pair.second.second) {
                auto& diag = context.addDiag(diag::PortDoesNotExist,
                                             pair.second.first->name.location());
                diag << pair.second.first->name.valueText();
                diag << checker.name;
            }
        }
    }

    // Now add all members.
    for (auto member : checkerSyntax->as<CheckerDeclarationSyntax>().members)
        body->addMembers(*member);

    auto instance = comp.emplace<CheckerInstanceSymbol>(name, loc, *body);
    instance->arrayPath = path.copy(comp);
    instance->setSyntax(syntax);
    instance->setAttributes(*context.scope, attributes);
    instance->connections = connections.copy(comp);
    return *instance;
}

CheckerInstanceSymbol& CheckerInstanceSymbol::createInvalid(const CheckerSymbol& checker,
                                                            uint32_t depth) {
    auto scope = checker.getParentScope();
    SLANG_ASSERT(scope);

    auto& comp = scope->getCompilation();
    auto assertionDetails = comp.allocAssertionDetails();
    assertionDetails->symbol = &checker;
    assertionDetails->instanceLoc = checker.location;

    ASTContext context(*scope, LookupLocation::after(checker));
    auto body = comp.emplace<CheckerInstanceBodySymbol>(comp, checker, *assertionDetails, context,
                                                        depth,
                                                        /* isProcedural */ false,
                                                        InstanceFlags::Uninstantiated);

    auto checkerSyntax = checker.getSyntax();
    SLANG_ASSERT(checkerSyntax);
    body->setSyntax(*checkerSyntax);

    SmallVector<Connection> connections;
    for (auto port : checker.ports) {
        if (port->name.empty())
            continue;

        const ExpressionSyntax* outputInitialSyntax = nullptr;
        auto actualArg = createCheckerFormal(comp, *port, *body, outputInitialSyntax, context);

        assertionDetails->argumentMap.emplace(
            actualArg, std::make_tuple((const PropertyExprSyntax*)nullptr, context));
        connections.emplace_back(*body, *actualArg, outputInitialSyntax,
                                 std::span<const AttributeSymbol* const>{});
    }

    for (auto member : checkerSyntax->as<CheckerDeclarationSyntax>().members)
        body->addMembers(*member);

    auto instance = comp.emplace<CheckerInstanceSymbol>(checker.name, checker.location, *body);
    instance->setSyntax(*checkerSyntax);
    instance->connections = connections.copy(comp);
    return *instance;
}

std::span<const CheckerInstanceSymbol::Connection> CheckerInstanceSymbol::getPortConnections()
    const {
    if (connectionsResolved)
        return connections;

    connectionsResolved = true;

    // We prepopulated some of the connection members but still need
    // to resolve the actual argument value and save it.
    for (auto& conn : connections) {
        conn.getOutputInitialExpr();

        auto argIt = body.assertionDetails.argumentMap.find(&conn.formal);
        SLANG_ASSERT(argIt != body.assertionDetails.argumentMap.end());

        auto& [expr, argCtx] = argIt->second;
        if (!expr)
            continue;

        if (conn.formal.kind == SymbolKind::AssertionPort) {
            AssertionInstanceExpression::ActualArg actualArgValue;
            if (AssertionInstanceExpression::checkAssertionArg(
                    *expr, conn.formal.as<AssertionPortSymbol>(), argCtx, actualArgValue,
                    /* isRecursiveProp */ false)) {
                conn.actual = actualArgValue;
            }
        }
        else if (auto exprSyntax = argCtx.requireSimpleExpr(*expr)) {
            ASTContext context = argCtx;
            if (!body.isProcedural)
                context.flags |= ASTFlags::NonProcedural;

            if (body.flags.has(InstanceFlags::FromBind))
                context.flags |= ASTFlags::BindInstantiation;

            auto& formal = conn.formal.as<FormalArgumentSymbol>();
            conn.actual = &Expression::bindArgument(formal.getType(), formal.direction, {},
                                                    *exprSyntax, context);
        }
    }

    return connections;
}

const Expression* CheckerInstanceSymbol::Connection::getOutputInitialExpr() const {
    if (!outputInitialExpr) {
        if (outputInitialSyntax) {
            ASTContext context(parent, LookupLocation::after(formal));
            outputInitialExpr = &Expression::bind(*outputInitialSyntax, context);
        }
        else {
            outputInitialExpr = nullptr;
        }
    }
    return *outputInitialExpr;
}

class CheckerMemberVisitor : public ASTVisitor<CheckerMemberVisitor, true, true> {
public:
    CheckerMemberVisitor(const CheckerInstanceBodySymbol& body) : body(body) {}

    void handle(const ProceduralBlockSymbol& symbol) {
        // Everything is allowed in final blocks, and implicit procedures created
        // for assertions should be ignored.
        if (symbol.procedureKind == ProceduralBlockKind::Final || symbol.isFromAssertion)
            return;

        if (symbol.procedureKind == ProceduralBlockKind::Always) {
            body.addDiag(diag::AlwaysInChecker, symbol.location);
            return;
        }

        SLANG_ASSERT(!currBlock);
        currBlock = &symbol;
        visitDefault(symbol);
        currBlock = nullptr;
    }

    void handle(const VariableSymbol& symbol) {
        inAssignmentRhs = true;
        visitDefault(symbol);
        inAssignmentRhs = false;
    }

    void handle(const AssignmentExpression& expr) {
        // Special checking only applies to assignments to checker variables.
        if (auto sym = expr.left().getSymbolReference(); sym && isFromChecker(*sym)) {
            expr.left().visit(*this);

            auto prev = std::exchange(inAssignmentRhs, true);
            expr.right().visit(*this);
            inAssignmentRhs = prev;
            return;
        }

        visitDefault(expr);
    }

    void handle(const CallExpression& expr) {
        if (inAssignmentRhs && expr.hasOutputArgs())
            body.addDiag(diag::CheckerFuncArg, expr.sourceRange);

        visitDefault(expr);
    }

    void handle(const NamedValueExpression& expr) {
        if (currBlock && expr.symbol.getType().isCovergroup()) {
            auto& diag = body.addDiag(diag::CheckerCovergroupProc, expr.sourceRange);
            diag.addNote(diag::NoteDeclarationHere, expr.symbol.location);
        }
        visitDefault(expr);
    }

    void handle(const HierarchicalValueExpression& expr) {
        bool inForkJoin = false;
        auto scope = expr.symbol.getParentScope();
        while (scope) {
            auto& sym = scope->asSymbol();
            if (sym.kind != SymbolKind::StatementBlock)
                break;

            if (sym.as<StatementBlockSymbol>().blockKind != StatementBlockKind::Sequential) {
                inForkJoin = true;
                break;
            }

            scope = sym.getParentScope();
        }

        if (inForkJoin && !isFromChecker(expr.symbol)) {
            auto& diag = body.addDiag(diag::CheckerForkJoinRef, expr.sourceRange);
            diag.addNote(diag::NoteDeclarationHere, expr.symbol.location);
            return;
        }

        visitDefault(expr);
    }

    template<typename T>
        requires(IsAnyOf<T, ElementSelectExpression, RangeSelectExpression>)
    void handle(const T& expr) {
        if (!expr.value().type->hasFixedRange() && !expr.bad()) {
            if (auto sym = expr.value().getSymbolReference(); sym && !isFromChecker(*sym)) {
                auto& diag = body.addDiag(diag::DynamicFromChecker, expr.sourceRange);
                diag.addNote(diag::NoteDeclarationHere, sym->location);
                return;
            }
        }
        visitDefault(expr);
    }

    void handle(const MemberAccessExpression& expr) {
        auto& valueType = *expr.value().type;
        if ((!valueType.isFixedSize() || valueType.isClass()) && !expr.bad()) {
            if (auto sym = expr.value().getSymbolReference(); sym && !isFromChecker(*sym)) {
                auto& diag = body.addDiag(diag::DynamicFromChecker, expr.sourceRange);
                diag.addNote(diag::NoteDeclarationHere, sym->location);
                return;
            }
        }
        visitDefault(expr);
    }

    template<std::derived_from<Statement> T>
    void handle(const T& stmt) {
        if (!currBlock)
            return;

        auto notAllowed = [&] {
            auto& diag = body.addDiag(diag::InvalidStmtInChecker, stmt.sourceRange);
            diag << SemanticFacts::getProcedureKindStr(currBlock->procedureKind);
        };

        auto checkTimed = [&] {
            auto& timed = stmt.template as<TimedStatement>();
            switch (timed.timing.kind) {
                case TimingControlKind::Invalid:
                case TimingControlKind::SignalEvent:
                case TimingControlKind::EventList:
                case TimingControlKind::ImplicitEvent:
                    return true;
                default:
                    body.addDiag(diag::CheckerTimingControl, timed.sourceRange);
                    return false;
            }
        };

        if (currBlock->procedureKind == ProceduralBlockKind::Initial) {
            switch (stmt.kind) {
                case StatementKind::Empty:
                case StatementKind::List:
                    break;
                case StatementKind::Timed:
                    if (!checkTimed())
                        return;
                    break;
                case StatementKind::Block:
                    if (stmt.template as<BlockStatement>().blockKind !=
                        StatementBlockKind::Sequential) {
                        return notAllowed();
                    }
                    break;
                case StatementKind::ImmediateAssertion:
                case StatementKind::ConcurrentAssertion:
                case StatementKind::ProceduralChecker:
                    return;
                default:
                    return notAllowed();
            }
        }
        else {
            switch (stmt.kind) {
                case StatementKind::Empty:
                case StatementKind::List:
                case StatementKind::Return:
                case StatementKind::Continue:
                case StatementKind::Break:
                case StatementKind::Conditional:
                case StatementKind::Case:
                case StatementKind::ForLoop:
                case StatementKind::RepeatLoop:
                case StatementKind::ForeachLoop:
                case StatementKind::WhileLoop:
                case StatementKind::DoWhileLoop:
                case StatementKind::ForeverLoop:
                    break;
                case StatementKind::Timed:
                    if (!checkTimed())
                        return;
                    break;
                case StatementKind::ExpressionStatement: {
                    auto& expr = stmt.template as<ExpressionStatement>().expr;
                    switch (expr.kind) {
                        case ExpressionKind::Call:
                            break;
                        case ExpressionKind::Assignment:
                            if (!expr.template as<AssignmentExpression>().isNonBlocking() &&
                                currBlock->procedureKind == ProceduralBlockKind::AlwaysFF) {
                                body.addDiag(diag::CheckerBlockingAssign, stmt.sourceRange);
                                return;
                            }
                            break;
                        default:
                            return notAllowed();
                    }
                    break;
                }
                case StatementKind::Block:
                    if (stmt.template as<BlockStatement>().blockKind !=
                        StatementBlockKind::Sequential) {
                        return notAllowed();
                    }
                    break;
                case StatementKind::ImmediateAssertion:
                case StatementKind::ConcurrentAssertion:
                case StatementKind::ProceduralChecker:
                    return;
                default:
                    return notAllowed();
            }
        }

        visitDefault(stmt);
    }

    // Ignore instances so we don't go down a rabbit hole for invalid constructions.
    void handle(const CheckerInstanceSymbol&) {}
    void handle(const InstanceSymbol&) {}

private:
    bool isFromChecker(const Symbol& symbol) const {
        auto scope = symbol.getParentScope();
        while (scope) {
            if (scope == &body)
                return true;

            auto& sym = scope->asSymbol();
            if (sym.kind == SymbolKind::InstanceBody)
                break;

            scope = sym.getParentScope();
        }
        return false;
    }

    const CheckerInstanceBodySymbol& body;
    const ProceduralBlockSymbol* currBlock = nullptr;
    bool inAssignmentRhs = false;
};

void CheckerInstanceSymbol::verifyMembers() const {
    CheckerMemberVisitor visitor(body);
    body.visit(visitor);
}

void CheckerInstanceSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("body", body);

    serializer.startArray("connections");
    for (auto& conn : getPortConnections()) {
        serializer.startObject();

        serializer.writeLink("formal", conn.formal);
        std::visit(
            [&](auto&& arg) {
                if (arg)
                    serializer.write("actual", *arg);
            },
            conn.actual);

        if (!conn.attributes.empty()) {
            serializer.startArray("attributes");
            for (auto attr : conn.attributes)
                serializer.serialize(*attr);
            serializer.endArray();
        }

        serializer.endObject();
    }
    serializer.endArray();
}

CheckerInstanceBodySymbol::CheckerInstanceBodySymbol(Compilation& compilation,
                                                     const CheckerSymbol& checker,
                                                     AssertionInstanceDetails& assertionDetails,
                                                     const ASTContext& originalContext,
                                                     uint32_t instanceDepth, bool isProcedural,
                                                     bitmask<InstanceFlags> flags) :
    Symbol(SymbolKind::CheckerInstanceBody, checker.name, checker.location),
    Scope(compilation, this), checker(checker), assertionDetails(assertionDetails),
    instanceDepth(instanceDepth), isProcedural(isProcedural), flags(flags),
    originalContext(originalContext) {

    assertionDetails.prevContext = &this->originalContext;

    auto parent = checker.getParentScope();
    SLANG_ASSERT(parent);
    setParent(*parent, checker.getIndex());
}

void CheckerInstanceBodySymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("checker", checker);
    serializer.write("isProcedural", isProcedural);
}

} // namespace slang::ast
