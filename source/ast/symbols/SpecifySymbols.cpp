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
#include "slang/ast/EvalContext.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

static void createImplicitNets(const SystemTimingCheckSymbol& timingCheck,
                               const SystemTimingCheckDef* def, const Scope& scope,
                               SmallVector<const Symbol*>& results,
                               SmallSet<std::string_view, 8>& implicitNetNames);

SpecifyBlockSymbol::SpecifyBlockSymbol(Compilation& compilation, SourceLocation loc) :
    Symbol(SymbolKind::SpecifyBlock, "", loc), Scope(compilation, this) {
}

SpecifyBlockSymbol& SpecifyBlockSymbol::fromSyntax(const Scope& scope,
                                                   const SpecifyBlockSyntax& syntax,
                                                   SmallVector<const Symbol*>& implicitSymbols) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<SpecifyBlockSymbol>(comp, syntax.specify.location());
    result->setSyntax(syntax);

    for (auto member : syntax.items)
        result->addMembers(*member);

    SmallSet<std::string_view, 8> implicitNetNames;

    for (auto member = result->getFirstMember(); member; member = member->getNextSibling()) {
        if (member->kind == SymbolKind::Specparam) {
            // specparams inside specify blocks get visibility in the parent scope as well.
            implicitSymbols.push_back(comp.emplace<TransparentMemberSymbol>(*member));
        }
        else if (member->kind == SymbolKind::SystemTimingCheck) {
            // some system timing checks can create implicit nets
            auto& timingCheck = member->as<SystemTimingCheckSymbol>();
            createImplicitNets(timingCheck, timingCheck.def, scope, implicitSymbols,
                               implicitNetNames);
        }
    }

    return *result;
}

bool SpecifyBlockSymbol::checkPathTerminal(const ValueSymbol& terminal, const Type& type,
                                           const Scope& specifyParent, SpecifyTerminalDir dir,
                                           SourceRange sourceRange) {
    // Type must be integral.
    if (!type.isIntegral()) {
        if (!type.isError())
            specifyParent.addDiag(diag::InvalidSpecifyType, sourceRange) << terminal.name << type;
        return false;
    }

    auto reportErr = [&] {
        auto code = dir == SpecifyTerminalDir::Input ? diag::InvalidSpecifySource
                                                     : diag::InvalidSpecifyDest;
        auto& diag = specifyParent.addDiag(code, sourceRange) << terminal.name;
        diag.addNote(diag::NoteDeclarationHere, terminal.location);
    };

    // Inputs must be nets (or modport ports) and outputs must
    // be nets or variables (or modport ports).
    if (terminal.kind != SymbolKind::Net && terminal.kind != SymbolKind::ModportPort &&
        (terminal.kind != SymbolKind::Variable || dir == SpecifyTerminalDir::Input)) {
        reportErr();
        return false;
    }

    if (terminal.kind == SymbolKind::ModportPort) {
        // Check that the modport port has the correct direction.
        auto portDir = terminal.as<ModportPortSymbol>().direction;
        if (portDir != ArgumentDirection::InOut &&
            ((dir == SpecifyTerminalDir::Input && portDir != ArgumentDirection::In) ||
             (dir == SpecifyTerminalDir::Output && portDir != ArgumentDirection::Out))) {
            reportErr();
            return false;
        }
        return true;
    }

    auto terminalParentScope = terminal.getParentScope();
    SLANG_ASSERT(terminalParentScope);

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
    if (&terminalParent != &specifyParent.asSymbol()) {
        specifyParent.addDiag(diag::InvalidSpecifyPath, sourceRange);
        return false;
    }

    if (dir == SpecifyTerminalDir::Both)
        return true;

    // Check that the terminal is connected to a module port and that
    // the direction is correct.
    for (auto portRef = terminal.getFirstPortBackref(); portRef;
         portRef = portRef->getNextBackreference()) {
        auto portDir = portRef->port->direction;
        if (portDir == ArgumentDirection::InOut ||
            (dir == SpecifyTerminalDir::Input && portDir == ArgumentDirection::In) ||
            (dir == SpecifyTerminalDir::Output && portDir == ArgumentDirection::Out)) {
            return true;
        }
    }

    reportErr();
    return false;
}

TimingPathSymbol::TimingPathSymbol(SourceLocation loc, ConnectionKind connectionKind,
                                   Polarity polarity, Polarity edgePolarity,
                                   EdgeKind edgeIdentifier) :
    Symbol(SymbolKind::TimingPath, ""sv, loc), connectionKind(connectionKind), polarity(polarity),
    edgePolarity(edgePolarity), edgeIdentifier(edgeIdentifier) {
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

static const Expression* bindTerminal(const ExpressionSyntax& syntax,
                                      SpecifyBlockSymbol::SpecifyTerminalDir dir,
                                      const Scope* parentParent, ASTContext& context) {
    auto expr = &Expression::bind(syntax, context);
    if (expr->bad())
        return nullptr;

    const Expression* valueExpr;
    switch (expr->kind) {
        case ExpressionKind::ElementSelect:
            valueExpr = &expr->as<ElementSelectExpression>().value();
            break;
        case ExpressionKind::RangeSelect:
            valueExpr = &expr->as<RangeSelectExpression>().value();
            break;
        default:
            valueExpr = expr;
            break;
    }

    if (valueExpr->kind != ExpressionKind::NamedValue) {
        auto code = (valueExpr->kind == ExpressionKind::ElementSelect ||
                     valueExpr->kind == ExpressionKind::RangeSelect)
                        ? diag::SpecifyPathMultiDim
                        : diag::InvalidSpecifyPath;
        context.addDiag(code, syntax.sourceRange());
    }
    else {
        auto& symbol = valueExpr->as<NamedValueExpression>().symbol;
        if (SpecifyBlockSymbol::checkPathTerminal(symbol, *expr->type, *parentParent, dir,
                                                  valueExpr->sourceRange)) {
            return expr;
        }
    }

    return nullptr;
}

static std::span<const Expression* const> bindTerminals(
    const SeparatedSyntaxList<NameSyntax>& syntaxList, SpecifyBlockSymbol::SpecifyTerminalDir dir,
    const Scope* parentParent, ASTContext& context) {

    SmallVector<const Expression*> results;
    for (auto exprSyntax : syntaxList) {
        auto expr = bindTerminal(*exprSyntax, dir, parentParent, context);
        if (expr)
            results.push_back(expr);
    }
    return results.copy(context.getCompilation());
}

// Only a subset of expressions are allowed to be used in specify path conditions.
struct SpecifyConditionVisitor {
    const ASTContext& context;
    const Scope* specifyParentScope;
    bool hasWarned = false;

    SpecifyConditionVisitor(const ASTContext& context, const Scope* specifyParentScope) :
        context(context), specifyParentScope(specifyParentScope) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            if (expr.bad())
                return;

            switch (expr.kind) {
                case ExpressionKind::NamedValue:
                    if (auto sym = expr.getSymbolReference()) {
                        // Specparams are always allowed.
                        if (sym->kind == SymbolKind::Specparam)
                            break;

                        // Other references must be locally defined nets or variables.
                        if ((sym->kind != SymbolKind::Net && sym->kind != SymbolKind::Variable) ||
                            sym->getParentScope() != specifyParentScope) {
                            auto& diag = context.addDiag(diag::SpecifyPathBadReference,
                                                         expr.sourceRange);
                            diag << sym->name;
                            diag.addNote(diag::NoteDeclarationHere, sym->location);
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
                    if constexpr (HasVisitExprs<T, SpecifyConditionVisitor>)
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
        if (!hasWarned) {
            context.addDiag(diag::SpecifyPathConditionExpr, sourceRange);
            hasWarned = true;
        }
    }
};

void TimingPathSymbol::resolve() const {
    isResolved = true;

    auto syntaxPtr = getSyntax();
    auto parent = getParentScope();
    SLANG_ASSERT(syntaxPtr && parent);

    auto parentParent = parent->asSymbol().getParentScope();
    auto& comp = parent->getCompilation();
    ASTContext context(*parent, LookupLocation::after(*this),
                       ASTFlags::NonProcedural | ASTFlags::SpecifyBlock);

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
    inputs = bindTerminals(syntax.desc->inputs, SpecifyBlockSymbol::SpecifyTerminalDir::Input,
                           parentParent, context);

    if (syntax.desc->suffix->kind == SyntaxKind::EdgeSensitivePathSuffix) {
        auto& esps = syntax.desc->suffix->as<EdgeSensitivePathSuffixSyntax>();
        outputs = bindTerminals(esps.outputs, SpecifyBlockSymbol::SpecifyTerminalDir::Output,
                                parentParent, context);

        // This expression is apparently allowed to be anything the user wants.
        edgeSourceExpr = &Expression::bind(*esps.expr, context);
    }
    else {
        outputs = bindTerminals(syntax.desc->suffix->as<SimplePathSuffixSyntax>().outputs,
                                SpecifyBlockSymbol::SpecifyTerminalDir::Output, parentParent,
                                context);
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
            context.eval(expr);
        }
    }

    delays = delayBuf.copy(comp);
}

void TimingPathSymbol::checkDuplicatePaths(TimingPathMap& timingPathMap) const {
    auto parent = getParentScope();
    SLANG_ASSERT(parent);

    EvalContext evalCtx(ASTContext(*parent, LookupLocation::max), EvalFlags::CacheResults);

    auto terminalOverlaps = [&](const Symbol& ourTerminal,
                                const std::optional<ConstantRange>& ourRange,
                                const Expression& otherExpr, bool& identicalRanges) {
        if (otherExpr.getSymbolReference() != &ourTerminal)
            return false;

        auto otherRange = otherExpr.evalSelector(evalCtx, /* enforceBounds */ false);
        identicalRanges = ourRange == otherRange;
        return !ourRange || !otherRange || ourRange->overlaps(*otherRange);
    };

    auto checkDup = [&](const TimingPathSymbol& otherPath, bool identicalRanges,
                        const Expression& inputExpr, const Expression& outputExpr,
                        const Expression& otherInputExpr, const Expression& otherOutputExpr) {
        // If these are literally the same path then it's not a dup, it's just ourselves.
        if (&inputExpr == &otherInputExpr && &outputExpr == &otherOutputExpr)
            return;

        // We've determined that our path and the `otherPath` have overlapping
        // source and dest terminals. If ranges are identical then we may not
        // have a dup, so check further.
        if (identicalRanges) {
            // If the paths have unique edges then they aren't dups.
            if (edgeIdentifier != otherPath.edgeIdentifier)
                return;

            // If one is conditional and the other is not, it's not a dup
            // unless the conditional one is also an ifnone condition.
            auto cond = getConditionExpr();
            auto otherCond = otherPath.getConditionExpr();
            if (isStateDependent != otherPath.isStateDependent) {
                if (cond || otherCond)
                    return;
            }
            else if (isStateDependent && otherPath.isStateDependent) {
                // If one is ifnone and the other is not, then not a dup.
                if ((!cond || !otherCond) && (cond || otherCond))
                    return;

                // If both are ifnone then there's a dup, otherwise check further.
                if (cond && otherCond) {
                    // If the condition makes this unique then it's not a dup.
                    // The LRM doesn't specify what it means for the condition expression
                    // to be unique; we check here at the syntactical level rather than
                    // the AST level.
                    auto lsyntax = cond->syntax;
                    auto rsyntax = otherCond->syntax;
                    if (lsyntax && rsyntax && !lsyntax->isEquivalentTo(*rsyntax))
                        return;
                }
            }
        }

        // Otherwise we've definitely found a dup, so issue a diagnostic.
        auto& diag = parent->addDiag(diag::DupTimingPath, inputExpr.sourceRange)
                     << outputExpr.sourceRange;
        diag.addNote(diag::NotePreviousDefinition, otherInputExpr.sourceRange)
            << otherOutputExpr.sourceRange;
    };

    for (auto outputExpr : getOutputs()) {
        if (auto output = outputExpr->getSymbolReference()) {
            // Find all paths that map to this output.
            auto& inputMap = timingPathMap[output];
            auto outputRange = outputExpr->evalSelector(evalCtx, /* enforceBounds */ false);

            for (auto inputExpr : getInputs()) {
                if (auto input = inputExpr->getSymbolReference()) {
                    // Find all paths that also map to this input.
                    auto& vec = inputMap[input];
                    auto inputRange = inputExpr->evalSelector(evalCtx, /* enforceBounds */ false);

                    // Look at each existing path and determine whether it's a duplicate.
                    bool alreadyAdded = false;
                    for (auto path : vec) {
                        for (auto otherOutputExpr : path->getOutputs()) {
                            // Only a dup if the output terminals overlap.
                            bool outputRangeIdentical;
                            if (terminalOverlaps(*output, outputRange, *otherOutputExpr,
                                                 outputRangeIdentical)) {
                                for (auto otherInputExpr : path->getInputs()) {
                                    // Only a dup if the input terminals overlap.
                                    bool inputRangeIdentical;
                                    if (terminalOverlaps(*input, inputRange, *otherInputExpr,
                                                         inputRangeIdentical)) {
                                        checkDup(*path, outputRangeIdentical && inputRangeIdentical,
                                                 *inputExpr, *outputExpr, *otherInputExpr,
                                                 *otherOutputExpr);
                                    }
                                }
                            }
                        }

                        // It's possible that *this* path can already be in the list,
                        // since you can have a declaration like this:
                        // (a[0], a[1] *> b) = 1
                        if (path == this)
                            alreadyAdded = true;
                    }

                    if (!alreadyAdded)
                        vec.push_back(this);
                }
            }
        }
    }
}

static std::string_view toString(TimingPathSymbol::Polarity polarity) {
    switch (polarity) {
        case TimingPathSymbol::Polarity::Unknown:
            return "Unknown"sv;
        case TimingPathSymbol::Polarity::Positive:
            return "Positive"sv;
        case TimingPathSymbol::Polarity::Negative:
            return "Negative"sv;
        default:
            SLANG_UNREACHABLE;
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

PulseStyleSymbol::PulseStyleSymbol(SourceLocation loc, PulseStyleKind pulseStyleKind) :
    Symbol(SymbolKind::PulseStyle, ""sv, loc), pulseStyleKind(pulseStyleKind) {
}

PulseStyleSymbol& PulseStyleSymbol::fromSyntax(const Scope& parent,
                                               const PulseStyleDeclarationSyntax& syntax) {
    auto pulseStyleKind = SemanticFacts::getPulseStyleKind(syntax.keyword.kind);

    auto& comp = parent.getCompilation();
    auto result = comp.emplace<PulseStyleSymbol>(syntax.getFirstToken().location(), pulseStyleKind);
    result->setSyntax(syntax);
    return *result;
}

void PulseStyleSymbol::resolve() const {
    isResolved = true;

    auto syntaxPtr = getSyntax();
    auto parent = getParentScope();
    SLANG_ASSERT(syntaxPtr && parent);

    auto parentParent = parent->asSymbol().getParentScope();
    ASTContext context(*parent, LookupLocation::after(*this),
                       ASTFlags::NonProcedural | ASTFlags::SpecifyBlock);

    auto& syntax = syntaxPtr->as<PulseStyleDeclarationSyntax>();
    terminals = bindTerminals(syntax.inputs, SpecifyBlockSymbol::SpecifyTerminalDir::Output,
                              parentParent, context);
}

void PulseStyleSymbol::checkPreviouslyUsed(const TimingPathMap& timingPathMap) const {
    auto parent = getParentScope();
    auto syntax = getSyntax();
    SLANG_ASSERT(parent && syntax);

    for (auto terminal : getTerminals()) {
        if (auto symbol = terminal->getSymbolReference()) {
            if (auto it = timingPathMap.find(symbol); it != timingPathMap.end()) {
                if (!it->second.empty() && !it->second.begin()->second.empty()) {
                    SourceRange pathRange;
                    auto first = it->second.begin()->second.front();
                    for (auto outputExpr : first->getOutputs()) {
                        if (outputExpr->getSymbolReference() == symbol) {
                            pathRange = outputExpr->sourceRange;
                            break;
                        }
                    }

                    SLANG_ASSERT(pathRange != SourceRange());

                    auto& diag = parent->addDiag(diag::InvalidPulseStyle, terminal->sourceRange);
                    diag << syntax->as<PulseStyleDeclarationSyntax>().keyword.valueText();
                    diag << symbol->name;
                    diag.addNote(diag::NoteDeclarationHere, pathRange);
                }
            }
        }
    }
}

void PulseStyleSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("pulseStyleKind", toString(pulseStyleKind));
}

struct SystemTimingCheckArgDef {
    enum ArgKind { Event, Notifier, DelayedRef, Limit, Condition } kind;

    bool requirePositive = false;
    int signalRef = -1;
    bool requireEdge = false;

    static SystemTimingCheckArgDef limit(bool requirePositive) { return {Limit, requirePositive}; }
    static SystemTimingCheckArgDef delayedRef(int index) { return {DelayedRef, false, index}; }
    static SystemTimingCheckArgDef controlledEvent() {
        return {Event, false, -1, /* requireEdge */ true};
    }
};

struct SystemTimingCheckDef {
    SystemTimingCheckKind kind;
    size_t minArgs;
    std::vector<SystemTimingCheckArgDef> args;
};

static flat_hash_map<std::string_view, SystemTimingCheckDef> createTimingCheckDefs() {
    using Arg = SystemTimingCheckArgDef;

    SystemTimingCheckDef setup{SystemTimingCheckKind::Setup,
                               3,
                               {{Arg::Event}, {Arg::Event}, Arg::limit(true), {Arg::Notifier}}};

    SystemTimingCheckDef hold{SystemTimingCheckKind::Hold,
                              3,
                              {{Arg::Event}, {Arg::Event}, Arg::limit(true), {Arg::Notifier}}};

    SystemTimingCheckDef setupHold{SystemTimingCheckKind::SetupHold,
                                   4,
                                   {{Arg::Event},
                                    {Arg::Event},
                                    Arg::limit(false),
                                    Arg::limit(false),
                                    {Arg::Notifier},
                                    {Arg::Condition},
                                    {Arg::Condition},
                                    Arg::delayedRef(0),
                                    Arg::delayedRef(1)}};

    SystemTimingCheckDef recovery{SystemTimingCheckKind::Recovery,
                                  3,
                                  {{Arg::Event}, {Arg::Event}, Arg::limit(true), {Arg::Notifier}}};

    SystemTimingCheckDef removal{SystemTimingCheckKind::Removal,
                                 3,
                                 {{Arg::Event}, {Arg::Event}, Arg::limit(true), {Arg::Notifier}}};

    SystemTimingCheckDef recRem{SystemTimingCheckKind::RecRem,
                                4,
                                {{Arg::Event},
                                 {Arg::Event},
                                 Arg::limit(false),
                                 Arg::limit(false),
                                 {Arg::Notifier},
                                 {Arg::Condition},
                                 {Arg::Condition},
                                 Arg::delayedRef(0),
                                 Arg::delayedRef(1)}};

    SystemTimingCheckDef skew{SystemTimingCheckKind::Skew,
                              3,
                              {{Arg::Event}, {Arg::Event}, Arg::limit(true), {Arg::Notifier}}};

    SystemTimingCheckDef timeSkew{SystemTimingCheckKind::TimeSkew,
                                  3,
                                  {{Arg::Event},
                                   {Arg::Event},
                                   Arg::limit(true),
                                   {Arg::Notifier},
                                   {Arg::Limit},
                                   {Arg::Limit}}};

    SystemTimingCheckDef fullSkew{SystemTimingCheckKind::FullSkew,
                                  4,
                                  {{Arg::Event},
                                   {Arg::Event},
                                   Arg::limit(true),
                                   Arg::limit(true),
                                   {Arg::Notifier},
                                   {Arg::Limit},
                                   {Arg::Limit}}};

    SystemTimingCheckDef period{SystemTimingCheckKind::Period,
                                2,
                                {Arg::controlledEvent(), Arg::limit(true), {Arg::Notifier}}};

    SystemTimingCheckDef width{
        SystemTimingCheckKind::Width,
        2,
        {Arg::controlledEvent(), Arg::limit(true), Arg::limit(true), {Arg::Notifier}}};

    SystemTimingCheckDef noChange{
        SystemTimingCheckKind::NoChange,
        4,
        {Arg::controlledEvent(), {Arg::Event}, {Arg::Limit}, {Arg::Limit}, {Arg::Notifier}}};

    return {{"$setup"sv, std::move(setup)},         {"$hold"sv, std::move(hold)},
            {"$setuphold"sv, std::move(setupHold)}, {"$recovery"sv, std::move(recovery)},
            {"$removal"sv, std::move(removal)},     {"$recrem"sv, std::move(recRem)},
            {"$skew"sv, std::move(skew)},           {"$timeskew"sv, std::move(timeSkew)},
            {"$fullskew"sv, std::move(fullSkew)},   {"$period"sv, std::move(period)},
            {"$width"sv, std::move(width)},         {"$nochange"sv, std::move(noChange)}};
}

static const flat_hash_map<std::string_view, SystemTimingCheckDef> SystemTimingCheckDefs =
    createTimingCheckDefs();

static void createImplicitNets(const SystemTimingCheckSymbol& timingCheck,
                               const SystemTimingCheckDef* def, const Scope& scope,
                               SmallVector<const Symbol*>& results,
                               SmallSet<std::string_view, 8>& implicitNetNames) {
    // If no default nettype is set, we don't create implicit nets.
    auto& netType = scope.getDefaultNetType();
    if (netType.isError() || !def)
        return;

    auto syntaxPtr = timingCheck.getSyntax();
    SLANG_ASSERT(syntaxPtr);

    auto& syntax = syntaxPtr->as<SystemTimingCheckSyntax>();
    auto& actualArgs = syntax.args;
    auto& formalArgs = def->args;

    ASTContext context(scope, LookupLocation::max);
    SmallVector<const IdentifierNameSyntax*> implicitNets;
    using Arg = SystemTimingCheckArgDef;

    for (size_t i = 0; i < actualArgs.size(); i++) {
        if (i >= formalArgs.size())
            break;

        auto& formal = formalArgs[i];
        auto& actual = *actualArgs[i];

        if (formal.kind == Arg::Event || formal.kind == Arg::Condition ||
            formal.kind == Arg::DelayedRef) {
            if (actual.kind == SyntaxKind::ExpressionTimingCheckArg) {
                Expression::findPotentiallyImplicitNets(
                    *actual.as<ExpressionTimingCheckArgSyntax>().expr, context, implicitNets);
            }
            else if (actual.kind == SyntaxKind::TimingCheckEventArg) {
                auto& eventArg = actual.as<TimingCheckEventArgSyntax>();
                Expression::findPotentiallyImplicitNets(*eventArg.terminal, context, implicitNets);

                if (eventArg.condition) {
                    Expression::findPotentiallyImplicitNets(*eventArg.condition->expr, context,
                                                            implicitNets);
                }
            }
        }
    }

    auto& comp = context.getCompilation();
    for (auto ins : implicitNets) {
        if (implicitNetNames.emplace(ins->identifier.valueText()).second)
            results.push_back(&NetSymbol::createImplicit(comp, *ins, netType));
    }
}

SystemTimingCheckSymbol::SystemTimingCheckSymbol(SourceLocation loc,
                                                 const SystemTimingCheckDef* def) :
    Symbol(SymbolKind::SystemTimingCheck, ""sv, loc), def(def) {
    timingCheckKind = def ? def->kind : SystemTimingCheckKind::Unknown;
}

SystemTimingCheckSymbol& SystemTimingCheckSymbol::fromSyntax(
    const Scope& parent, const SystemTimingCheckSyntax& syntax) {

    const SystemTimingCheckDef* def;
    if (auto it = SystemTimingCheckDefs.find(syntax.name.valueText());
        it != SystemTimingCheckDefs.end()) {
        def = &it->second;
    }
    else {
        parent.addDiag(diag::UnknownSystemTimingCheck, syntax.name.range())
            << syntax.name.valueText();
        def = nullptr;
    }

    auto& comp = parent.getCompilation();
    auto result = comp.emplace<SystemTimingCheckSymbol>(syntax.getFirstToken().location(), def);
    result->setSyntax(syntax);
    return *result;
}

void SystemTimingCheckSymbol::resolve() const {
    isResolved = true;
    if (!def)
        return;

    auto syntaxPtr = getSyntax();
    auto parent = getParentScope();
    SLANG_ASSERT(syntaxPtr && parent);

    auto parentParent = parent->asSymbol().getParentScope();
    auto& comp = parent->getCompilation();
    ASTContext context(*parent, LookupLocation::after(*this),
                       ASTFlags::NonProcedural | ASTFlags::SpecifyBlock);

    auto& syntax = syntaxPtr->as<SystemTimingCheckSyntax>();
    auto& actualArgs = syntax.args;
    auto& formalArgs = def->args;

    if (actualArgs.size() < def->minArgs) {
        auto& diag = context.addDiag(diag::TooFewArguments, syntax.sourceRange());
        diag << syntax.name.valueText();
        diag << def->minArgs << actualArgs.size();
        return;
    }

    if (actualArgs.size() > formalArgs.size()) {
        auto& diag = context.addDiag(diag::TooManyArguments, syntax.sourceRange());
        diag << syntax.name.valueText();
        diag << formalArgs.size();
        diag << actualArgs.size();
        return;
    }

    SmallVector<Arg> argBuf;
    for (size_t i = 0; i < actualArgs.size(); i++) {
        auto& formal = formalArgs[i];
        auto& actual = *actualArgs[i];
        if (actual.kind == SyntaxKind::EmptyTimingCheckArg) {
            if (i < def->minArgs)
                context.addDiag(diag::EmptyArgNotAllowed, actualArgs[i]->sourceRange());
            argBuf.emplace_back();
            continue;
        }

        if (actual.kind == SyntaxKind::TimingCheckEventArg &&
            formal.kind != SystemTimingCheckArgDef::Event) {
            context.addDiag(diag::TimingCheckEventNotAllowed, actual.sourceRange());
            argBuf.emplace_back();
            continue;
        }

        switch (formal.kind) {
            case SystemTimingCheckArgDef::Limit: {
                auto& expr = Expression::bind(*actual.as<ExpressionTimingCheckArgSyntax>().expr,
                                              context);
                argBuf.emplace_back(expr);

                auto val = context.eval(expr);
                if (val && formal.requirePositive) {
                    if ((val.isInteger() && val.integer().isSigned() &&
                         val.integer().isNegative()) ||
                        (val.isReal() && val.real() < 0.0) ||
                        (val.isShortReal() && val.shortReal() < 0.0f)) {
                        context.addDiag(diag::NegativeTimingLimit, expr.sourceRange) << val;
                    }
                }
                break;
            }
            case SystemTimingCheckArgDef::Condition: {
                auto& expr = Expression::bind(*actual.as<ExpressionTimingCheckArgSyntax>().expr,
                                              context);
                context.requireBooleanConvertible(expr);
                argBuf.emplace_back(expr);
                break;
            }
            case SystemTimingCheckArgDef::Notifier: {
                // Needs to be a simple identifier, referencing an integral lvalue
                auto& exprSyntax = *actual.as<ExpressionTimingCheckArgSyntax>().expr;
                if (exprSyntax.kind != SyntaxKind::IdentifierName) {
                    context.addDiag(diag::InvalidTimingCheckNotifierArg, actual.sourceRange());
                    argBuf.emplace_back();
                    break;
                }

                ASTContext nonContinuous = context;
                nonContinuous.flags &= ~ASTFlags::NonProcedural;

                auto& expr = Expression::bindLValue(exprSyntax, comp.getLogicType(),
                                                    exprSyntax.getFirstToken().location(),
                                                    nonContinuous, /* isInout */ false);
                argBuf.emplace_back(expr);
                break;
            }
            case SystemTimingCheckArgDef::Event:
                if (actual.kind == SyntaxKind::ExpressionTimingCheckArg) {
                    auto expr = bindTerminal(*actual.as<ExpressionTimingCheckArgSyntax>().expr,
                                             SpecifyBlockSymbol::SpecifyTerminalDir::Both,
                                             parentParent, context);
                    if (!expr)
                        argBuf.emplace_back();
                    else
                        argBuf.emplace_back(*expr);
                }
                else {
                    auto& eventArg = actual.as<TimingCheckEventArgSyntax>();
                    auto expr = bindTerminal(*eventArg.terminal,
                                             SpecifyBlockSymbol::SpecifyTerminalDir::Both,
                                             parentParent, context);

                    const Expression* condition = nullptr;
                    if (eventArg.condition) {
                        condition = &Expression::bind(*eventArg.condition->expr, context);
                        context.requireBooleanConvertible(*condition);
                    }

                    auto edge = SemanticFacts::getEdgeKind(eventArg.edge.kind);

                    SmallVector<EdgeDescriptor> edgeDescriptors;
                    if (eventArg.controlSpecifier) {
                        for (auto descSyntax : eventArg.controlSpecifier->descriptors) {
                            auto t1 = descSyntax->t1.rawText();
                            auto t2 = descSyntax->t2.rawText();
                            if (t1.length() + t2.length() != 2)
                                continue;

                            EdgeDescriptor desc;
                            memcpy(desc.data(), t1.data(), t1.length());
                            if (!t2.empty())
                                memcpy(desc.data() + t1.length(), t2.data(), t2.length());

                            edgeDescriptors.push_back(desc);
                        }
                    }

                    argBuf.emplace_back(*expr, condition, edge, edgeDescriptors.copy(comp));
                }

                if (formal.requireEdge && argBuf.back().expr) {
                    auto edge = argBuf.back().edge;
                    if (edge == EdgeKind::None) {
                        context.addDiag(diag::TimingCheckEventEdgeRequired,
                                        argBuf.back().expr->sourceRange)
                            << syntax.name.valueText();
                    }
                    else if (def->kind == SystemTimingCheckKind::NoChange &&
                             edge == EdgeKind::BothEdges) {
                        context.addDiag(diag::NoChangeEdgeRequired,
                                        actual.as<TimingCheckEventArgSyntax>().edge.range());
                    }
                }
                break;
            case SystemTimingCheckArgDef::DelayedRef: {
                SLANG_ASSERT(formal.signalRef >= 0 && formal.signalRef < int(i));
                auto signalExpr = argBuf[size_t(formal.signalRef)].expr;
                if (!signalExpr) {
                    argBuf.emplace_back();
                    break;
                }

                auto& exprSyntax = *actual.as<ExpressionTimingCheckArgSyntax>().expr;
                auto& expr = Expression::bindLValue(exprSyntax, *signalExpr->type,
                                                    exprSyntax.getFirstToken().location(), context,
                                                    /* isInout */ false);
                argBuf.emplace_back(expr);
                break;
            }
            default:
                SLANG_UNREACHABLE;
        }
    }

    args = argBuf.copy(comp);
}

void SystemTimingCheckSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("timingCheckKind", toString(timingCheckKind));

    serializer.startArray("arguments");
    for (auto& arg : getArguments()) {
        serializer.startObject();
        if (arg.expr)
            serializer.write("expr", *arg.expr);
        if (arg.condition)
            serializer.write("condition", *arg.condition);
        if (arg.edge != EdgeKind::None)
            serializer.write("edge", toString(arg.edge));

        if (!arg.edgeDescriptors.empty()) {
            serializer.startArray("edgeDescriptors");
            for (auto& desc : arg.edgeDescriptors)
                serializer.serialize(std::string_view(desc.data(), desc.size()));
            serializer.endArray();
        }

        serializer.endObject();
    }
    serializer.endArray();
}

} // namespace slang::ast
