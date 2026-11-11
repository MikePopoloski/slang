// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"
#include "fmt/ranges.h"
#include <boost_regex.hpp>
#include <charconv>

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/ValueDriver.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::analysis;
using namespace slang::syntax;

namespace dff_name {

// Returns the part of the name before the first suffix it ends with, or nothing when the name
// ends with none of the suffixes or is only a suffix.
std::optional<std::string_view> getNameBeforeSuffix(std::string_view name,
                                                    const std::vector<std::string>& suffixes) {
    for (const auto& suffix : suffixes) {
        if (name.ends_with(suffix)) {
            if (name.size() == suffix.size())
                return std::nullopt;
            return name.substr(0, name.size() - suffix.size());
        }
    }
    return std::nullopt;
}

// Splits a trailing pipeline stage number off a name: "data_q2" gives {"data_q", 2}.
// A name without a stage number of 1 or more gives stage 0.
std::pair<std::string_view, uint64_t> splitPipelineStage(std::string_view name) {
    const auto nameWithoutStage = name.substr(0, name.find_last_not_of("0123456789") + 1);
    uint64_t stage = 0;
    std::from_chars(name.data() + nameWithoutStage.size(), name.data() + name.size(), stage);
    if (stage == 0)
        return {name, 0};
    return {nameWithoutStage, stage};
}

// Returns the source text of a syntax node without whitespace or comments: "a || b" gives "a||b".
std::string getTextWithoutWhitespace(const SyntaxNode& syntax) {
    return SyntaxPrinter().setIncludeTrivia(false).print(syntax).str();
}

// Returns the register that the left-hand side writes only part of, such as state_q for
// state_q[i].count or data_q[3:0], or nothing when it writes a whole variable.
const Symbol* getPartiallyAssignedRegister(const Expression& lhs) {
    const Expression* expression = &lhs;
    while (true) {
        switch (expression->kind) {
            case ExpressionKind::MemberAccess:
                expression = &expression->as<MemberAccessExpression>().value();
                break;
            case ExpressionKind::ElementSelect:
                expression = &expression->as<ElementSelectExpression>().value();
                break;
            case ExpressionKind::RangeSelect:
                expression = &expression->as<RangeSelectExpression>().value();
                break;
            default:
                return expression == &lhs ? nullptr : expression->getSymbolReference();
        }
    }
}

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, VisitFlags::AllCanonical> {
    const AnalysisManager& analysisManager;
    const TidyConfig::CheckConfigs& checkConfigs;
    bool insideAlwaysFF = false;

    MainVisitor(Diagnostics& diagnostics, const AnalysisManager& analysisManager) :
        TidyVisitor(diagnostics), analysisManager(analysisManager),
        checkConfigs(config.getCheckConfigs()) {}

    void handle(const ProceduralBlockSymbol& block) {
        NEEDS_SKIP_SYMBOL(block)
        insideAlwaysFF = block.procedureKind == ProceduralBlockKind::AlwaysFF;
        visitDefault(block);
        insideAlwaysFF = false;
    }

    void handle(const ConditionalStatement& statement) {
        const auto& predicate = statement.syntax->as<ConditionalStatementSyntax>().predicate;
        const auto& waivedConditions = checkConfigs.dffWaiveIfConditions;
        const bool isWaived = std::ranges::find(waivedConditions,
                                                getTextWithoutWhitespace(*predicate)) !=
                              waivedConditions.end();
        if (!isWaived)
            visitDefault(statement);
        else if (statement.ifFalse)
            statement.ifFalse->visit(*this);
    }

    void handle(const AssignmentExpression& assignment) {
        if (!insideAlwaysFF)
            return;

        if (assignment.isNonBlocking())
            checkFlipFlopAssignment(assignment);
        else if (auto symbol = assignment.left().getSymbolReference())
            reportIfFlipFlopOutputName(*symbol, assignment.left().sourceRange.start());
    }

    void handle(const UnaryExpression& expression) {
        const auto op = expression.op;
        const bool isIncrementOrDecrement = op == UnaryOperator::Preincrement ||
                                            op == UnaryOperator::Predecrement ||
                                            op == UnaryOperator::Postincrement ||
                                            op == UnaryOperator::Postdecrement;
        const auto& operand = expression.operand();
        const auto symbol = operand.getSymbolReference();
        if (!insideAlwaysFF || !isIncrementOrDecrement || !symbol)
            return;

        const bool isLocal = symbol->kind == SymbolKind::Variable &&
                             symbol->as<VariableSymbol>().lifetime == VariableLifetime::Automatic;
        if (!isLocal &&
            !boost::regex_match(std::string(symbol->name), checkConfigs.dffWaiveLhsRegexPattern)) {
            diags.add(diag::DFFName, operand.sourceRange.start())
                << symbol->name
                << std::string_view("is incremented or decremented inside always_ff; assign it "
                                    "with a nonblocking assignment instead");
        }
    }

    void handle(const VariableSymbol& variable) {
        NEEDS_SKIP_SYMBOL(variable)
        checkDriversOutsideAlwaysFF(variable);
    }

    void handle(const NetSymbol& net) {
        NEEDS_SKIP_SYMBOL(net)
        if (net.getInitializer())
            reportIfFlipFlopOutputName(net, net.location);
        checkDriversOutsideAlwaysFF(net);
    }

private:
    void checkDriversOutsideAlwaysFF(const ValueSymbol& symbol) {
        for (const auto driver : analysisManager.getDrivers(symbol)) {
            if (driver->source != DriverSource::AlwaysFF && !driver->isUnidirectionalPort() &&
                !driver->flags.has(DriverFlags::Initializer)) {
                reportIfFlipFlopOutputName(symbol, driver->getSourceRange().start());
            }
        }
    }

    void reportIfFlipFlopOutputName(const Symbol& symbol, SourceLocation location) {
        if (getNameBeforeSuffix(symbol.name, checkConfigs.dffOutputSuffix)) {
            diags.add(diag::DFFName, location)
                << symbol.name
                << std::string_view("has a flip-flop output suffix but is not driven by a "
                                    "nonblocking assignment inside always_ff");
        }
    }

    std::optional<std::string_view> getVariableNameOutsideMacro(
        const Expression& expression) const {
        if (!ValueExpressionBase::isKind(expression.kind) ||
            sourceManager->isMacroLoc(expression.sourceRange.start())) {
            return std::nullopt;
        }
        return expression.as<ValueExpressionBase>().symbol.name;
    }

    void reportMissingSuffix(const ExpressionSyntax& syntax, const std::string& text,
                             const std::vector<std::string>& suffixes) {
        diags.add(diag::DFFName, syntax.sourceRange().start())
            << text << fmt::format("should be a variable whose name ends with one of {}", suffixes);
    }

    void checkFlipFlopAssignment(const AssignmentExpression& assignment) {
        const auto& assignmentSyntax = assignment.syntax->as<BinaryExpressionSyntax>();
        if (sourceManager->isMacroLoc(assignmentSyntax.operatorToken.location()))
            return;

        const auto& outputSuffix = checkConfigs.dffOutputSuffix;
        const auto& inputSuffix = checkConfigs.dffInputSuffix;
        const auto lhsText = getTextWithoutWhitespace(*assignmentSyntax.left);
        if (outputSuffix.empty() ||
            boost::regex_match(lhsText, checkConfigs.dffWaiveLhsRegexPattern))
            return;

        const auto partiallyAssignedRegister = getPartiallyAssignedRegister(assignment.left());
        if (partiallyAssignedRegister) {
            diags.add(diag::DFFName, assignmentSyntax.left->sourceRange().start())
                << lhsText
                << fmt::format("is part of a register; assign the whole register '{}' in "
                               "always_ff instead",
                               partiallyAssignedRegister->name);
            return;
        }

        const auto [lhsNameWithoutStage, lhsStage] = splitPipelineStage(
            getVariableNameOutsideMacro(assignment.left()).value_or(""));
        const auto lhsNameBeforeSuffix = getNameBeforeSuffix(lhsNameWithoutStage, outputSuffix);
        if (!lhsNameBeforeSuffix) {
            reportMissingSuffix(*assignmentSyntax.left, lhsText, outputSuffix);
            return;
        }

        const auto rhsText = getTextWithoutWhitespace(*assignmentSyntax.right);
        const auto& rhs = assignment.right().unwrapImplicitConversions();
        const auto rhsName = getVariableNameOutsideMacro(rhs).value_or("");
        if (lhsStage > 1) {
            const auto previousStage = fmt::format("{}{}", lhsNameWithoutStage, lhsStage - 1);
            const bool isFedByUnnumberedStage = lhsStage == 2 && rhsName == lhsNameWithoutStage;
            if (rhsName != previousStage && !isFedByUnnumberedStage) {
                diags.add(diag::DFFName, assignmentSyntax.right->sourceRange().start())
                    << rhsText
                    << fmt::format("should be the previous pipeline stage '{}'", previousStage);
            }
            return;
        }

        if (inputSuffix.empty())
            return;

        const auto rhsNameBeforeSuffix = getNameBeforeSuffix(rhsName, inputSuffix);
        if (!rhsNameBeforeSuffix)
            reportMissingSuffix(*assignmentSyntax.right, rhsText, inputSuffix);
        else if (*rhsNameBeforeSuffix != *lhsNameBeforeSuffix) {
            diags.add(diag::DFFName, assignmentSyntax.left->sourceRange().start())
                << lhsText
                << fmt::format("has a different name before its suffix than its input '{}'",
                               rhsText);
        }
    }
};
} // namespace dff_name

using namespace dff_name;
class DFFName : public TidyCheck {
public:
    [[maybe_unused]] explicit DFFName(TidyKind kind,
                                      std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const AnalysisManager& analysisManager) override {
        MainVisitor visitor(diagnostics, analysisManager);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::DFFName; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override { return "'{}' {}"; }
    std::string name() const override { return "DFFName"; }
    std::string description() const override {
        return "Enforces that each nonblocking assignment inside always_ff assigns a variable "
               "with a flip-flop output suffix (" +
               fmt::format(fmt::emphasis::italic, "dffOutputSuffix") +
               ") from a variable with a flip-flop input suffix (" +
               fmt::format(fmt::emphasis::italic, "dffInputSuffix") +
               ") and the same name before the suffix, such as data_q <= data_d. A trailing "
               "number marks a pipeline stage, which takes its value from the previous stage, "
               "such as data_q2 <= data_q1. Assign a register as a whole, not one member, element "
               "or bit range at a time. Variables with a flip-flop output suffix must not be "
               "driven anywhere else, and always_ff must not increment or decrement a variable "
               "declared outside it. Assignments in the true branch of an if whose condition is "
               "in " +
               fmt::format(fmt::emphasis::italic, "dffWaiveIfConditions") +
               " or whose left-hand side matches " +
               fmt::format(fmt::emphasis::italic, "dffWaiveLhsRegexString") + " are not checked\n";
    }
    std::string shortDescription() const override {
        return "Enforces flip-flop input and output naming suffixes";
    }
};

REGISTER(DFFName, DFFName, TidyKind::Style)
