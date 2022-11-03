//------------------------------------------------------------------------------
// SpecifySymbols.cpp
// Contains specify block symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/SpecifySymbols.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

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

TimingPathSymbol::TimingPathSymbol(SourceLocation loc, ConnectionKind connectionKind,
                                   Polarity polarity, Polarity edgePolarity,
                                   EdgeKind edgeIdentifier) :
    Symbol(SymbolKind::TimingPath, ""sv, loc),
    connectionKind(connectionKind), polarity(polarity), edgePolarity(edgePolarity),
    edgeIdentifier(edgeIdentifier) {
}

TimingPathSymbol& TimingPathSymbol::fromSyntax(const Scope& parent,
                                               const PathDeclarationSyntax& syntax) {
    Polarity polarity;
    switch (syntax.desc->polarityOperator.kind) {
        case TokenKind::Plus:
        case TokenKind::PlusEqual:
            polarity = Polarity::Positive;
            break;
        case TokenKind::Minus:
        case TokenKind::MinusEqual:
            polarity = Polarity::Negative;
            break;
        default:
            polarity = Polarity::Unknown;
            break;
    }

    auto connectionKind = syntax.desc->pathOperator.kind == TokenKind::StarArrow
                              ? ConnectionKind::Full
                              : ConnectionKind::Parallel;

    auto edgeIdentifier = SemanticFacts::getEdgeKind(syntax.desc->edgeIdentifier.kind);

    auto edgePolarity = Polarity::Unknown;
    if (syntax.desc->suffix->kind == SyntaxKind::EdgeSensitivePathSuffix) {
        auto& esps = syntax.desc->suffix->as<EdgeSensitivePathSuffixSyntax>();
        switch (esps.polarityOperator.kind) {
            case TokenKind::Plus:
            case TokenKind::PlusColon:
                edgePolarity = Polarity::Positive;
                break;
            case TokenKind::Minus:
            case TokenKind::MinusColon:
                edgePolarity = Polarity::Negative;
                break;
            default:
                break;
        }
    }

    auto& comp = parent.getCompilation();
    auto result = comp.emplace<TimingPathSymbol>(syntax.getFirstToken().location(), connectionKind,
                                                 polarity, edgePolarity, edgeIdentifier);
    result->setSyntax(syntax);
    return *result;
}

TimingPathSymbol& TimingPathSymbol::fromSyntax(const Scope& parent,
                                               const IfNonePathDeclarationSyntax& syntax) {
    auto& result = fromSyntax(parent, *syntax.path);
    result.setSyntax(syntax);
    result.isStateDependent = true;
    return result;
}

TimingPathSymbol& TimingPathSymbol::fromSyntax(const Scope& parent,
                                               const ConditionalPathDeclarationSyntax& syntax) {
    auto& result = fromSyntax(parent, *syntax.path);
    result.setSyntax(syntax);
    result.isStateDependent = true;
    return result;
}

static bool checkPathTerminal(const ValueSymbol& terminal, const Symbol& specifyParent,
                              ASTContext& context, bool isSource, SourceRange sourceRange) {
    // Type must be integral.
    auto& type = terminal.getType();
    if (!type.isIntegral()) {
        if (!type.isError())
            context.addDiag(diag::InvalidSpecifyType, sourceRange) << terminal.name << type;
        return false;
    }

    auto reportErr = [&] {
        auto code = isSource ? diag::InvalidSpecifySource : diag::InvalidSpecifyDest;
        auto& diag = context.addDiag(code, sourceRange) << terminal.name;
        diag.addNote(diag::NoteDeclarationHere, terminal.location);
    };

    // Inputs must be nets (or modport ports) and outputs must
    // be nets or variables (or modport ports).
    if (terminal.kind != SymbolKind::Net && terminal.kind != SymbolKind::ModportPort &&
        (terminal.kind != SymbolKind::Variable || isSource)) {
        reportErr();
        return false;
    }

    if (terminal.kind == SymbolKind::ModportPort) {
        // Check that the modport port has the correct direction.
        auto dir = terminal.as<ModportPortSymbol>().direction;
        if (dir != ArgumentDirection::InOut && ((isSource && dir != ArgumentDirection::In) ||
                                                (!isSource && dir != ArgumentDirection::Out))) {
            reportErr();
        }
        return false;
    }

    auto terminalParentScope = terminal.getParentScope();
    ASSERT(terminalParentScope);

    auto& terminalParent = terminalParentScope->asSymbol();
    if (terminalParent.kind == SymbolKind::InstanceBody &&
        terminalParent.as<InstanceBodySymbol>().getDefinition().definitionKind ==
            DefinitionKind::Interface) {
        // If the signal is part of an interface then the only way we could have accessed
        // it is through an interface port, in which case the direction is "inout" and
        // therefore fine no matter whether this is an input or output terminal.
        return true;
    }

    // If we get here then the terminal must be a member of the module containing
    // our parent specify block.
    if (&terminalParent != &specifyParent) {
        context.addDiag(diag::InvalidSpecifyPath, sourceRange);
        return false;
    }

    // TODO: check that the terminal is connected to a module port and that
    // the direction is correct.
    return true;
}

// Only a subset of expressions are allowed to be used in specify path conditions.
struct SpecifyConditionVisitor {
    const ASTContext& context;
    const Scope* specifyParentScope;
    bool hasError = false;

    SpecifyConditionVisitor(const ASTContext& context, const Scope* specifyParentScope) :
        context(context), specifyParentScope(specifyParentScope) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            switch (expr.kind) {
                case ExpressionKind::NamedValue:
                    if (auto sym = expr.getSymbolReference()) {
                        // Specparams are always allowed.
                        if (sym->kind == SymbolKind::Specparam || hasError)
                            break;

                        // Other references must be locally defined nets or variables.
                        if ((sym->kind != SymbolKind::Net && sym->kind != SymbolKind::Variable) ||
                            sym->getParentScope() != specifyParentScope) {
                            auto& diag = context.addDiag(diag::SpecifyPathBadReference,
                                                         expr.sourceRange);
                            diag << sym->name;
                            diag.addNote(diag::NoteDeclarationHere, sym->location);
                            hasError = true;
                        }
                    }
                    break;
                case ExpressionKind::ElementSelect:
                case ExpressionKind::RangeSelect:
                case ExpressionKind::Call:
                case ExpressionKind::MinTypMax:
                case ExpressionKind::Concatenation:
                case ExpressionKind::Replication:
                case ExpressionKind::ConditionalOp:
                case ExpressionKind::UnaryOp:
                case ExpressionKind::BinaryOp:
                case ExpressionKind::Conversion:
                    if constexpr (is_detected_v<ASTDetectors::visitExprs_t, T,
                                                SpecifyConditionVisitor>)
                        expr.visitExprs(*this);

                    if (expr.kind == ExpressionKind::UnaryOp) {
                        switch (expr.template as<UnaryExpression>().op) {
                            case UnaryOperator::BitwiseNot:
                            case UnaryOperator::BitwiseAnd:
                            case UnaryOperator::BitwiseOr:
                            case UnaryOperator::BitwiseXor:
                            case UnaryOperator::BitwiseNand:
                            case UnaryOperator::BitwiseNor:
                            case UnaryOperator::BitwiseXnor:
                            case UnaryOperator::LogicalNot:
                                break;
                            default:
                                reportError(expr.sourceRange);
                        }
                    }
                    else if (expr.kind == ExpressionKind::BinaryOp) {
                        switch (expr.template as<BinaryExpression>().op) {
                            case BinaryOperator::BinaryAnd:
                            case BinaryOperator::BinaryOr:
                            case BinaryOperator::BinaryXor:
                            case BinaryOperator::BinaryXnor:
                            case BinaryOperator::Equality:
                            case BinaryOperator::Inequality:
                            case BinaryOperator::LogicalAnd:
                            case BinaryOperator::LogicalOr:
                                break;
                            default:
                                reportError(expr.sourceRange);
                        }
                    }
                    else if (expr.kind == ExpressionKind::Conversion) {
                        if (!expr.template as<ConversionExpression>().isImplicit())
                            reportError(expr.sourceRange);
                    }
                    break;
                case ExpressionKind::IntegerLiteral:
                case ExpressionKind::RealLiteral:
                    break;
                default:
                    reportError(expr.sourceRange);
                    break;
            }
        }
    }

    void reportError(SourceRange sourceRange) {
        if (!hasError) {
            context.addDiag(diag::SpecifyPathConditionExpr, sourceRange);
            hasError = true;
        }
    }

    void visitInvalid(const Expression&) {}
    void visitInvalid(const AssertionExpr&) {}
};

void TimingPathSymbol::resolve() const {
    isResolved = true;

    auto syntaxPtr = getSyntax();
    auto parent = getParentScope();
    ASSERT(syntaxPtr && parent);

    auto parentParent = parent->asSymbol().getParentScope();
    ASSERT(parentParent);

    auto& comp = parent->getCompilation();
    ASTContext context(*parent, LookupLocation::after(*this), ASTFlags::NonProcedural);

    auto bindTerminals = [&](const SeparatedSyntaxList<NameSyntax>& syntaxList, bool isSource) {
        SmallVector<const Expression*> results;
        for (auto exprSyntax : syntaxList) {
            auto expr = &Expression::bind(*exprSyntax, context);
            if (expr->bad())
                continue;

            switch (expr->kind) {
                case ExpressionKind::ElementSelect:
                    expr = &expr->as<ElementSelectExpression>().value();
                    break;
                case ExpressionKind::RangeSelect:
                    expr = &expr->as<RangeSelectExpression>().value();
                    break;
                default:
                    break;
            }

            if (expr->kind != ExpressionKind::NamedValue) {
                auto code = (expr->kind == ExpressionKind::ElementSelect ||
                             expr->kind == ExpressionKind::RangeSelect)
                                ? diag::SpecifyPathMultiDim
                                : diag::InvalidSpecifyPath;
                context.addDiag(code, exprSyntax->sourceRange());
            }
            else {
                auto& symbol = expr->as<NamedValueExpression>().symbol;
                if (checkPathTerminal(symbol, parentParent->asSymbol(), context, isSource,
                                      expr->sourceRange)) {
                    results.push_back(expr);
                }
            }
        }
        return results.copy(comp);
    };

    if (syntaxPtr->kind == SyntaxKind::IfNonePathDeclaration) {
        syntaxPtr = syntaxPtr->as<IfNonePathDeclarationSyntax>().path;
    }
    else if (syntaxPtr->kind == SyntaxKind::ConditionalPathDeclaration) {
        auto& conditional = syntaxPtr->as<ConditionalPathDeclarationSyntax>();
        syntaxPtr = conditional.path;

        conditionExpr = &Expression::bind(*conditional.predicate, context);
        if (context.requireBooleanConvertible(*conditionExpr)) {
            SpecifyConditionVisitor visitor(context, parentParent);
            conditionExpr->visit(visitor);
        }
    }

    auto& syntax = syntaxPtr->as<PathDeclarationSyntax>();
    inputs = bindTerminals(syntax.desc->inputs, true);

    if (syntax.desc->suffix->kind == SyntaxKind::EdgeSensitivePathSuffix) {
        auto& esps = syntax.desc->suffix->as<EdgeSensitivePathSuffixSyntax>();
        outputs = bindTerminals(esps.outputs, false);

        // This expression is apparently allowed to be anything the user wants.
        edgeSourceExpr = &Expression::bind(*esps.expr, context);
    }
    else {
        outputs = bindTerminals(syntax.desc->suffix->as<SimplePathSuffixSyntax>().outputs, false);
    }

    // Verify that input and output sizes match for parallel connections.
    // Parallel connections only allow one input and one output.
    if (connectionKind == ConnectionKind::Parallel && inputs.size() == 1 && outputs.size() == 1) {
        if (inputs[0]->type->getBitWidth() != outputs[0]->type->getBitWidth()) {
            auto& diag = context.addDiag(diag::ParallelPathWidth,
                                         syntax.desc->pathOperator.range());
            diag << inputs[0]->sourceRange << outputs[0]->sourceRange;
            diag << *inputs[0]->type << *outputs[0]->type;
        }
    }

    // Bind all delay values.
    SmallVector<const Expression*> delayBuf;
    for (auto delaySyntax : syntax.delays) {
        auto& expr = Expression::bind(*delaySyntax, context);
        if (!expr.bad()) {
            if (!expr.type->isNumeric()) {
                context.addDiag(diag::DelayNotNumeric, expr.sourceRange) << *expr.type;
                continue;
            }

            delayBuf.push_back(&expr);
            context.eval(expr, EvalFlags::SpecparamsAllowed);
        }
    }

    delays = delayBuf.copy(comp);
}

static string_view toString(TimingPathSymbol::Polarity polarity) {
    switch (polarity) {
        case TimingPathSymbol::Polarity::Unknown:
            return "Unknown"sv;
        case TimingPathSymbol::Polarity::Positive:
            return "Positive"sv;
        case TimingPathSymbol::Polarity::Negative:
            return "Negative"sv;
        default:
            ASSUME_UNREACHABLE;
    }
}

void TimingPathSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("connectionKind",
                     connectionKind == ConnectionKind::Full ? "Full"sv : "Parallel"sv);
    serializer.write("polarity", toString(polarity));
    serializer.write("edgePolarity", toString(edgePolarity));
    serializer.write("edgeIdentifier", toString(edgeIdentifier));
    serializer.write("isStateDependent", isStateDependent);

    if (auto expr = getEdgeSourceExpr())
        serializer.write("edgeSourceExpr", *expr);

    if (auto expr = getConditionExpr())
        serializer.write("conditionExpr", *expr);

    serializer.startArray("inputs");
    for (auto expr : getInputs())
        serializer.serialize(*expr);
    serializer.endArray();

    serializer.startArray("outputs");
    for (auto expr : getOutputs())
        serializer.serialize(*expr);
    serializer.endArray();

    serializer.startArray("delays");
    for (auto expr : getDelays())
        serializer.serialize(*expr);
    serializer.endArray();
}

} // namespace slang::ast
