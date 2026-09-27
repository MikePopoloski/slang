//------------------------------------------------------------------------------
// TautologicalCompare.cpp
// Checks for comparisons that always evaluate to the same result
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/TautologicalCompare.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;
using parsing::KnownSystemName;

namespace {

// A conservative description of the set of values an integral expression can
// take on. If nonNegative is set all values lie in [0, 2^width - 1], and
// otherwise they lie in [-2^(width-1), 2^(width-1) - 1].
//
// Note that this is deliberately not the same thing as Expression::getEffectiveWidth,
// which is an approximation tuned to avoid noisy width conversion warnings (for
// example it doesn't count carry bits from addition). Here we need a guaranteed
// bound on the possible values, since any imprecision results in false positives.
struct IntRange {
    bitwidth_t width = 0;
    bool nonNegative = true;

    // The number of bits needed to hold every value in the range
    // as a signed two's complement integer.
    bitwidth_t signedWidth() const { return nonNegative ? width + 1 : width; }

    static IntRange forType(const Type& type) { return {type.getBitWidth(), !type.isSigned()}; }

    static IntRange forValue(const SVInt& value) {
        if (value.isSigned() && value.isNegative())
            return {value.getMinRepresentedBits(), false};
        return {value.getActiveBits(), true};
    }

    // Returns the smallest range that contains all values of both given ranges.
    static IntRange join(IntRange a, IntRange b) {
        if (a.nonNegative && b.nonNegative)
            return {std::max(a.width, b.width), true};
        return {std::max(a.signedWidth(), b.signedWidth()), false};
    }

    // Takes a range describing the mathematical result of some operation
    // and returns the range of values that result has once it's stored in
    // the given type (which may cause it to wrap around).
    IntRange fitTo(const Type& type) const {
        auto typeWidth = type.getBitWidth();
        if (type.isSigned() ? signedWidth() <= typeWidth : (nonNegative && width <= typeWidth))
            return *this;
        return forType(type);
    }
};

// Exact math on the values of an integral type is done using signed SVInts that
// are one bit wider than the type, which is enough to represent every value of
// the type (as well as one past either end) without worrying about overflow.
struct ValueDomain {
    const bitwidth_t width;
    const bool isSigned;
    const IntRange typeRange;

    explicit ValueDomain(const Type& type) :
        width(type.getBitWidth() + 1), isSigned(type.isSigned()),
        typeRange(IntRange::forType(type)) {}

    // Converts a constant of the domain's type into the representation used for math.
    SVInt convert(const SVInt& value) const {
        SVInt result = value.extend(width, isSigned);
        result.setSigned(true);
        return result;
    }

    // Returns the smallest value in the given range.
    SVInt lowest(IntRange range) const {
        if (range.nonNegative)
            return SVInt(width, 0, true);
        return -SVInt(width, 1, true).shl(range.width - 1);
    }

    // Returns the largest value in the given range.
    SVInt highest(IntRange range) const {
        SVInt one(width, 1, true);
        return one.shl(range.nonNegative ? range.width : range.width - 1) - one;
    }

    // The smallest and largest values of the type.
    SVInt min() const { return lowest(typeRange); }
    SVInt max() const { return highest(typeRange); }
};

SVInt increment(SVInt value) {
    return ++value;
}

SVInt decrement(SVInt value) {
    return --value;
}

// Walks an expression tree and checks that every node in it satisfies
// the given predicate. Anything that isn't an expression (such as a
// pattern or timing control) automatically fails the check.
template<typename TPredicate>
struct AllNodesVisitor {
    TPredicate predicate;
    bool result = true;

    explicit AllNodesVisitor(TPredicate predicate) : predicate(predicate) {}

    template<typename T>
    void visit(const T& node) {
        if (!result)
            return;

        if constexpr (std::is_base_of_v<Expression, T>) {
            if (!predicate(node)) {
                result = false;
                return;
            }

            if constexpr (HasVisitExprs<T, AllNodesVisitor>)
                node.visitExprs(*this);
        }
        else {
            result = false;
        }
    }
};

template<typename TPredicate>
bool allNodes(const Expression& expr, TPredicate predicate) {
    AllNodesVisitor<TPredicate> visitor(predicate);
    expr.visit(visitor);
    return visitor.result;
}

// Returns true if evaluating the given expression node has no side effects
// and always produces the same value when evaluated twice in a row
// (not considering its children, which are checked separately).
bool isPureNode(const Expression& expr) {
    switch (expr.kind) {
        case ExpressionKind::IntegerLiteral:
        case ExpressionKind::RealLiteral:
        case ExpressionKind::TimeLiteral:
        case ExpressionKind::UnbasedUnsizedIntegerLiteral:
        case ExpressionKind::NullLiteral:
        case ExpressionKind::UnboundedLiteral:
        case ExpressionKind::StringLiteral:
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
        case ExpressionKind::BinaryOp:
        case ExpressionKind::ConditionalOp:
        case ExpressionKind::Inside:
        case ExpressionKind::Concatenation:
        case ExpressionKind::Replication:
        case ExpressionKind::Streaming:
        case ExpressionKind::ElementSelect:
        case ExpressionKind::RangeSelect:
        case ExpressionKind::MemberAccess:
        case ExpressionKind::Conversion:
        case ExpressionKind::DataType:
        case ExpressionKind::TypeReference:
        case ExpressionKind::ArbitrarySymbol:
        case ExpressionKind::SimpleAssignmentPattern:
        case ExpressionKind::StructuredAssignmentPattern:
        case ExpressionKind::ReplicatedAssignmentPattern:
        case ExpressionKind::ValueRange:
        case ExpressionKind::MinTypMax:
        case ExpressionKind::TaggedUnion:
            return true;
        case ExpressionKind::UnaryOp:
            return !OpInfo::isLValue(expr.as<UnaryExpression>().op);
        case ExpressionKind::Invalid:
        case ExpressionKind::Assignment:
        case ExpressionKind::LValueReference:
        case ExpressionKind::EmptyArgument:
        case ExpressionKind::Dist:
        case ExpressionKind::ClockingEvent:
        case ExpressionKind::AssertionInstance:
            return false;
        case ExpressionKind::Call:
            // We have no way of knowing whether an arbitrary function
            // (or system function, like $random) has side effects.
            return false;
        case ExpressionKind::NewArray:
        case ExpressionKind::NewClass:
        case ExpressionKind::NewCovergroup:
        case ExpressionKind::CopyClass:
            // These create a new object each time they're evaluated.
            return false;
    }
    SLANG_UNREACHABLE;
}

// Returns true if the given expression has no side effects and will
// always produce the same value when evaluated twice in a row.
bool isPure(const Expression& expr) {
    return allNodes(expr, isPureNode);
}

// Returns true if the given expression node is a literal or an operation
// that combines literals (not considering its children, which are checked separately).
bool isLiteralNode(const Expression& expr) {
    switch (expr.kind) {
        case ExpressionKind::IntegerLiteral:
        case ExpressionKind::UnbasedUnsizedIntegerLiteral:
        case ExpressionKind::BinaryOp:
        case ExpressionKind::ConditionalOp:
        case ExpressionKind::Concatenation:
        case ExpressionKind::Replication:
        case ExpressionKind::Conversion:
        case ExpressionKind::MinTypMax:
            return true;
        case ExpressionKind::NamedValue:
            // Enum values are allowed but parameters are deliberately excluded,
            // since their values can vary between instances and so a comparison
            // involving them may only be incidentally tautological.
            return expr.as<NamedValueExpression>().symbol.kind == SymbolKind::EnumValue;
        case ExpressionKind::UnaryOp:
            return !OpInfo::isLValue(expr.as<UnaryExpression>().op);
        case ExpressionKind::Invalid:
        case ExpressionKind::RealLiteral:
        case ExpressionKind::TimeLiteral:
        case ExpressionKind::NullLiteral:
        case ExpressionKind::UnboundedLiteral:
        case ExpressionKind::StringLiteral:
        case ExpressionKind::HierarchicalValue:
        case ExpressionKind::Inside:
        case ExpressionKind::Assignment:
        case ExpressionKind::Streaming:
        case ExpressionKind::ElementSelect:
        case ExpressionKind::RangeSelect:
        case ExpressionKind::MemberAccess:
        case ExpressionKind::Call:
        case ExpressionKind::DataType:
        case ExpressionKind::TypeReference:
        case ExpressionKind::ArbitrarySymbol:
        case ExpressionKind::LValueReference:
        case ExpressionKind::SimpleAssignmentPattern:
        case ExpressionKind::StructuredAssignmentPattern:
        case ExpressionKind::ReplicatedAssignmentPattern:
        case ExpressionKind::EmptyArgument:
        case ExpressionKind::ValueRange:
        case ExpressionKind::Dist:
        case ExpressionKind::NewArray:
        case ExpressionKind::NewClass:
        case ExpressionKind::NewCovergroup:
        case ExpressionKind::CopyClass:
        case ExpressionKind::ClockingEvent:
        case ExpressionKind::AssertionInstance:
        case ExpressionKind::TaggedUnion:
            return false;
    }
    SLANG_UNREACHABLE;
}

// Returns true if the given expression is a constant built entirely from
// literals (and enum values).
bool isLiteralConstant(const Expression& expr) {
    return allNodes(expr, isLiteralNode);
}

// Returns true for comparison operators whose operands we can reason about
// numerically (i.e. everything other than wildcard equality).
bool isNumericComparison(BinaryOperator op) {
    return OpInfo::isComparison(op) && op != BinaryOperator::WildcardEquality &&
           op != BinaryOperator::WildcardInequality;
}

// Returns the operator that gives the same result when the operands are swapped.
BinaryOperator flipOperands(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::LessThan:
            return BinaryOperator::GreaterThan;
        case BinaryOperator::LessThanEqual:
            return BinaryOperator::GreaterThanEqual;
        case BinaryOperator::GreaterThan:
            return BinaryOperator::LessThan;
        case BinaryOperator::GreaterThanEqual:
            return BinaryOperator::LessThanEqual;
        default:
            return op;
    }
}

std::string_view boolStr(bool value) {
    return value ? "true"sv : "false"sv;
}

// A comparison between some non-constant expression and a literal constant,
// normalized so that the constant is on the right hand side.
struct ConstCompare {
    const Expression* valueExpr;
    const Expression* constExpr;
    BinaryOperator op;
    SVInt constant;
};

// A set of values, used for reasoning about combinations of comparisons.
// This is either an inclusive range [lo, hi] or, if isExclusion is set,
// every value in the domain except for lo (in which case lo == hi).
struct ValueSet {
    SVInt lo;
    SVInt hi;
    bool isExclusion = false;
};

class Checker {
public:
    Checker(AnalysisContext& context, const Symbol& rootSymbol) :
        context(context), rootSymbol(rootSymbol), evalCtx(rootSymbol) {
        evalCtx.pushEmptyFrame();
    }

    void checkComparison(const BinaryExpression& expr) {
        if (checkSelfCompare(expr))
            return;

        auto cc = getConstCompare(expr);
        if (!cc)
            return;

        if (checkBitwiseCompare(expr, *cc))
            return;

        checkRangeCompare(expr, *cc);
    }

    void checkLogical(const BinaryExpression& expr) {
        if (checkNegation(expr))
            return;

        checkOverlap(expr);
    }

private:
    AnalysisContext& context;
    const Symbol& rootSymbol;
    EvalContext evalCtx;

    bool isConstant(const Expression& expr) { return bool(expr.eval(evalCtx)); }

    std::optional<SVInt> getLiteralConstant(const Expression& expr) {
        if (!isLiteralConstant(expr))
            return std::nullopt;

        auto cv = expr.eval(evalCtx);
        if (!cv.isInteger() || cv.integer().hasUnknown())
            return std::nullopt;

        return cv.integer();
    }

    std::optional<SVInt> getShiftAmount(const Expression& expr) {
        auto cv = expr.eval(evalCtx);
        if (!cv.isInteger() || cv.integer().hasUnknown() ||
            (cv.integer().isSigned() && cv.integer().isNegative())) {
            return std::nullopt;
        }
        return cv.integer();
    }

    std::optional<ConstCompare> getConstCompare(const BinaryExpression& expr) {
        if (!isNumericComparison(expr.op))
            return std::nullopt;

        auto& left = expr.left();
        auto& right = expr.right();
        if (!left.type->isIntegral())
            return std::nullopt;

        auto lc = getLiteralConstant(left);
        auto rc = getLiteralConstant(right);
        if (lc.has_value() == rc.has_value())
            return std::nullopt;

        auto& valueExpr = lc ? right : left;
        if (isConstant(valueExpr))
            return std::nullopt;

        if (lc)
            return ConstCompare{&right, &left, flipOperands(expr.op), std::move(*lc)};
        return ConstCompare{&left, &right, expr.op, std::move(*rc)};
    }

    // Checks for comparisons of an expression with itself, e.g. `x == x`.
    bool checkSelfCompare(const BinaryExpression& expr) {
        auto& left = expr.left();
        auto& right = expr.right();
        if (left.type->isFloating() || !left.isEquivalentTo(right) || !isPure(left) ||
            isConstant(left)) {
            return false;
        }

        bool result;
        switch (expr.op) {
            case BinaryOperator::CaseEquality:
            case BinaryOperator::WildcardEquality:
                result = true;
                break;
            case BinaryOperator::CaseInequality:
            case BinaryOperator::WildcardInequality:
            case BinaryOperator::Inequality:
            case BinaryOperator::LessThan:
            case BinaryOperator::GreaterThan:
                result = false;
                break;
            case BinaryOperator::Equality:
            case BinaryOperator::LessThanEqual:
            case BinaryOperator::GreaterThanEqual:
                // If the value has unknown bits these comparisons evaluate
                // to X, so they can be used (somewhat obscurely) to check for
                // unknowns and we shouldn't warn about them.
                if (left.type->isFourState())
                    return false;
                result = true;
                break;
            default:
                return false;
        }

        auto& diag = context.addDiag(rootSymbol, diag::SelfCompare, expr.opRange);
        diag << boolStr(result);
        diag << left.sourceRange << right.sourceRange;
        return true;
    }

    // Checks for bitwise operations that make an equality comparison
    // impossible, e.g. `(x & 4) == 8` or `(x | 4) == 1`.
    bool checkBitwiseCompare(const BinaryExpression& expr, const ConstCompare& cc) {
        bool isEquality;
        switch (cc.op) {
            case BinaryOperator::Equality:
            case BinaryOperator::CaseEquality:
                isEquality = true;
                break;
            case BinaryOperator::Inequality:
            case BinaryOperator::CaseInequality:
                isEquality = false;
                break;
            default:
                return false;
        }

        auto bitwise = cc.valueExpr->as_if<BinaryExpression>();
        if (!bitwise ||
            (bitwise->op != BinaryOperator::BinaryAnd && bitwise->op != BinaryOperator::BinaryOr)) {
            return false;
        }

        auto mask = getLiteralConstant(bitwise->right());
        if (!mask)
            mask = getLiteralConstant(bitwise->left());
        if (!mask || mask->getBitWidth() != cc.constant.getBitWidth())
            return false;

        // For AND, any bit set in the constant that's not set in the mask can never match.
        // For OR, any bit set in the mask that's not set in the constant can never match.
        SVInt extra = bitwise->op == BinaryOperator::BinaryAnd ? (cc.constant & ~*mask)
                                                               : (*mask & ~cc.constant);
        if (!extra.reductionOr())
            return false;

        auto& diag = context.addDiag(rootSymbol, diag::BitwiseCompare, expr.opRange);
        diag << boolStr(!isEquality);
        diag << cc.valueExpr->sourceRange << cc.constExpr->sourceRange;
        return true;
    }

    // Checks for comparisons against constants that are outside of (or
    // at the limits of) the range of values that the other side can take on,
    // e.g. `x < 16` where x is a 4-bit unsigned value.
    void checkRangeCompare(const BinaryExpression& expr, const ConstCompare& cc) {
        auto& type = *cc.valueExpr->type;
        auto range = getRange(*cc.valueExpr);

        ValueDomain domain(type);
        SVInt c = domain.convert(cc.constant);
        SVInt lo = domain.lowest(range);
        SVInt hi = domain.highest(range);

        const bool outOfRange = bool(c < lo || c > hi);
        std::optional<bool> result;
        switch (cc.op) {
            case BinaryOperator::Equality:
            case BinaryOperator::CaseEquality:
                if (outOfRange)
                    result = false;
                break;
            case BinaryOperator::Inequality:
            case BinaryOperator::CaseInequality:
                if (outOfRange)
                    result = true;
                break;
            case BinaryOperator::LessThan:
                if (hi < c)
                    result = true;
                else if (c <= lo)
                    result = false;
                break;
            case BinaryOperator::LessThanEqual:
                if (hi <= c)
                    result = true;
                else if (c < lo)
                    result = false;
                break;
            case BinaryOperator::GreaterThan:
                if (lo > c)
                    result = true;
                else if (c >= hi)
                    result = false;
                break;
            case BinaryOperator::GreaterThanEqual:
                if (lo >= c)
                    result = true;
                else if (c > hi)
                    result = false;
                break;
            default:
                break;
        }

        if (!result)
            return;

        // Comparisons right at the limit of the range are more likely to be
        // intentional when the constant comes from a macro, since the macro
        // value may be different in other configurations.
        if (!outOfRange && context.isFromMacroBody(cc.constExpr->sourceRange.start()))
            return;

        auto code = outOfRange ? diag::OutOfRangeCompare : diag::LimitCompare;
        auto& diag = context.addDiag(rootSymbol, code, expr.opRange);
        diag << range.width << (range.nonNegative ? "unsigned"sv : "signed"sv);
        diag << OpInfo::getText(cc.op) << cc.constant.toString(LiteralBase::Decimal, false);
        diag << boolStr(*result);
        diag << cc.valueExpr->sourceRange << cc.constExpr->sourceRange;
    }

    // Checks for things like `x || !x` and `x && !x`.
    bool checkNegation(const BinaryExpression& expr) {
        if (expr.op != BinaryOperator::LogicalAnd && expr.op != BinaryOperator::LogicalOr)
            return false;

        auto isNegationOf = [](const Expression& maybeNot, const Expression& other) {
            auto unary = maybeNot.as_if<UnaryExpression>();
            return unary && unary->op == UnaryOperator::LogicalNot &&
                   unary->operand().isEquivalentTo(other);
        };

        auto& left = expr.left();
        auto& right = expr.right();
        if (!isNegationOf(left, right) && !isNegationOf(right, left))
            return false;

        if (!isPure(left) || !isPure(right) || isConstant(left))
            return false;

        auto& diag = context.addDiag(rootSymbol, diag::NegationCompare, expr.opRange);
        diag << OpInfo::getText(expr.op) << boolStr(expr.op == BinaryOperator::LogicalOr);
        diag << left.sourceRange << right.sourceRange;
        return true;
    }

    // Returns the set of values of the domain of the given type that satisfy
    // the given comparison, or nullopt if that set can't be represented or
    // is trivially empty or full (which is diagnosed separately).
    static std::optional<ValueSet> getValueSet(const ConstCompare& cc, const ValueDomain& domain) {
        SVInt c = domain.convert(cc.constant);
        SVInt min = domain.min();
        SVInt max = domain.max();

        switch (cc.op) {
            case BinaryOperator::Equality:
            case BinaryOperator::CaseEquality:
                return ValueSet{c, c};
            case BinaryOperator::Inequality:
            case BinaryOperator::CaseInequality:
                return ValueSet{c, c, true};
            case BinaryOperator::LessThan:
                if (c <= min || c > max)
                    return std::nullopt;
                return ValueSet{min, decrement(c)};
            case BinaryOperator::LessThanEqual:
                if (c < min || c >= max)
                    return std::nullopt;
                return ValueSet{min, c};
            case BinaryOperator::GreaterThan:
                if (c < min || c >= max)
                    return std::nullopt;
                return ValueSet{increment(c), max};
            case BinaryOperator::GreaterThanEqual:
                if (c <= min || c > max)
                    return std::nullopt;
                return ValueSet{c, max};
            default:
                return std::nullopt;
        }
    }

    // Returns the complement of the given set within the given domain.
    // Only sets produced by getValueSet are supported.
    static ValueSet complement(const ValueSet& set, const ValueDomain& domain) {
        if (set.isExclusion)
            return ValueSet{set.lo, set.lo};

        SVInt min = domain.min();
        SVInt max = domain.max();
        if (set.lo == min)
            return ValueSet{increment(set.hi), max};
        if (set.hi == max)
            return ValueSet{min, decrement(set.lo)};

        SLANG_ASSERT(set.lo == set.hi);
        return ValueSet{set.lo, set.lo, true};
    }

    // Returns true if the intersection of the two sets is empty.
    static bool isDisjoint(const ValueSet& a, const ValueSet& b) {
        if (a.isExclusion && b.isExclusion)
            return false;
        if (a.isExclusion)
            return bool(b.lo == b.hi && b.lo == a.lo);
        if (b.isExclusion)
            return bool(a.lo == a.hi && a.lo == b.lo);
        return bool(a.lo > b.hi || b.lo > a.hi);
    }

    // Checks for logical combinations of comparisons against constants
    // that always produce the same result, e.g. `x < 5 && x > 10` or
    // `x != 1 || x != 2`.
    void checkOverlap(const BinaryExpression& expr) {
        bool isAnd;
        switch (expr.op) {
            case BinaryOperator::LogicalAnd:
            case BinaryOperator::BinaryAnd:
                isAnd = true;
                break;
            case BinaryOperator::LogicalOr:
            case BinaryOperator::BinaryOr:
                isAnd = false;
                break;
            default:
                return;
        }

        auto getCompare = [&](const Expression& operand) -> std::optional<ConstCompare> {
            auto binary = operand.unwrapImplicitConversions().as_if<BinaryExpression>();
            if (!binary)
                return std::nullopt;
            return getConstCompare(*binary);
        };

        auto lcc = getCompare(expr.left());
        if (!lcc)
            return;

        auto rcc = getCompare(expr.right());
        if (!rcc || !lcc->valueExpr->isEquivalentTo(*rcc->valueExpr) || !isPure(*lcc->valueExpr))
            return;

        // The value expressions are equivalent, so they have the same type.
        ValueDomain domain(*lcc->valueExpr->type);
        auto ls = getValueSet(*lcc, domain);
        auto rs = getValueSet(*rcc, domain);
        if (!ls || !rs)
            return;

        bool isTautology;
        if (isAnd) {
            isTautology = isDisjoint(*ls, *rs);
        }
        else {
            // The union of the two sets covers the whole domain
            // if the intersection of their complements is empty.
            isTautology = isDisjoint(complement(*ls, domain), complement(*rs, domain));
        }

        if (!isTautology)
            return;

        auto& diag = context.addDiag(rootSymbol, diag::OverlapCompare, expr.opRange);
        diag << (isAnd ? "non-overlapping"sv : "overlapping"sv) << boolStr(!isAnd);
        diag << expr.left().sourceRange << expr.right().sourceRange;
    }

    // Gets the range of values the given expression can take on.
    IntRange getRange(const Expression& expr) {
        SLANG_ASSERT(expr.type->isIntegral());

        // The computeRange functions below describe the mathematical result of each
        // operation; here we apply the effect of storing it in the expression's type,
        // which may cause it to wrap around.
        return computeRange(expr).fitTo(*expr.type);
    }

    IntRange computeRange(const Expression& expr) {
        auto& type = *expr.type;

        switch (expr.kind) {
            case ExpressionKind::IntegerLiteral:
            case ExpressionKind::UnbasedUnsizedIntegerLiteral:
                return getConstantRange(expr);
            case ExpressionKind::NamedValue:
                // Note that we deliberately don't look at parameter values here,
                // since they can differ between instances.
                if (expr.as<NamedValueExpression>().symbol.kind == SymbolKind::EnumValue)
                    return getConstantRange(expr);
                return IntRange::forType(type);
            case ExpressionKind::Conversion:
                return computeRange(expr.as<ConversionExpression>());
            case ExpressionKind::UnaryOp:
                return computeRange(expr.as<UnaryExpression>());
            case ExpressionKind::BinaryOp:
                return computeRange(expr.as<BinaryExpression>());
            case ExpressionKind::ConditionalOp: {
                auto& cond = expr.as<ConditionalExpression>();
                if (auto side = cond.knownSide())
                    return getSubRange(*side, type);
                return IntRange::join(getSubRange(cond.left(), type),
                                      getSubRange(cond.right(), type));
            }
            case ExpressionKind::Concatenation:
                return computeRange(expr.as<ConcatenationExpression>());
            case ExpressionKind::MinTypMax:
                return getSubRange(expr.as<MinTypMaxExpression>().selected(), type);
            case ExpressionKind::Call:
                return computeRange(expr.as<CallExpression>());
            default:
                return IntRange::forType(type);
        }
    }

    // Gets the range of an operand that is expected to already have been
    // converted to the given type. If that turns out to not be the case,
    // conservatively returns the full range of the type.
    IntRange getSubRange(const Expression& expr, const Type& type) {
        if (!expr.type->isEquivalent(type))
            return IntRange::forType(type);
        return getRange(expr);
    }

    IntRange getConstantRange(const Expression& expr) {
        auto cv = expr.eval(evalCtx);
        if (!cv.isInteger() || cv.integer().hasUnknown())
            return IntRange::forType(*expr.type);
        return IntRange::forValue(cv.integer());
    }

    IntRange computeRange(const CallExpression& call) {
        auto& type = *call.type;
        if (!call.isSystemCall())
            return IntRange::forType(type);

        auto& subroutine = *std::get<CallExpression::SystemCallInfo>(call.subroutine).subroutine;
        if (subroutine.knownNameId == KnownSystemName::Signed ||
            subroutine.knownNameId == KnownSystemName::Unsigned) {
            // These just reinterpret the bits of their argument.
            auto args = call.arguments();
            if (args.size() == 1 && args[0]->type->isIntegral() &&
                args[0]->type->getBitWidth() == type.getBitWidth()) {
                return getRange(*args[0]);
            }
        }
        else if (auto width = subroutine.getEffectiveWidth()) {
            // The effective width counts a sign bit only for negative values
            // (e.g. the associative array traversal methods can return -1, 0, or 1),
            // so a signed result needs one more bit to hold the whole range.
            if (type.isSigned())
                return {*width + 1, false};
            return {*width, true};
        }

        return IntRange::forType(type);
    }

    IntRange computeRange(const ConversionExpression& expr) {
        auto& type = *expr.type;
        auto& operand = expr.operand();
        auto& fromType = *operand.type;
        if (!fromType.isIntegral() || expr.conversionKind == ConversionKind::StreamingConcat ||
            expr.conversionKind == ConversionKind::BitstreamCast) {
            return IntRange::forType(type);
        }

        auto range = getRange(operand);
        auto fromWidth = fromType.getBitWidth();
        if (type.getBitWidth() > fromWidth && !(range.nonNegative && range.width < fromWidth)) {
            // We're extending a value whose top bit might be set, so we need
            // to know what kind of extension is happening. Propagated conversions
            // sign extend based on the target type, and other conversions sign
            // extend based on the source type [11.8.2].
            bool signExtend = expr.conversionKind == ConversionKind::Propagated
                                  ? type.isSigned()
                                  : fromType.isSigned();
            if (signExtend && !fromType.isSigned())
                range = {fromWidth, false};
            else if (!signExtend && fromType.isSigned())
                range = {fromWidth, true};
        }

        return range;
    }

    IntRange computeRange(const UnaryExpression& expr) {
        auto& type = *expr.type;
        switch (expr.op) {
            case UnaryOperator::Plus:
                return getSubRange(expr.operand(), type);
            case UnaryOperator::Minus: {
                auto r = getSubRange(expr.operand(), type);
                if (r.width == 0)
                    return r;
                return {r.width + 1, false};
            }
            case UnaryOperator::BitwiseNot: {
                // ~x == -x - 1
                auto r = getSubRange(expr.operand(), type);
                if (r.nonNegative)
                    return {r.width + 1, false};
                return r;
            }
            case UnaryOperator::LogicalNot:
            case UnaryOperator::BitwiseAnd:
            case UnaryOperator::BitwiseOr:
            case UnaryOperator::BitwiseXor:
            case UnaryOperator::BitwiseNand:
            case UnaryOperator::BitwiseNor:
            case UnaryOperator::BitwiseXnor:
                return {1, true};
            default:
                return IntRange::forType(type);
        }
    }

    // Note that a range with a width of zero means the value is known to be exactly
    // zero (e.g. from a literal 0 or from `x & 0`). The general formulas below are
    // all still correct in that case, but some of them would add an unnecessary
    // sign or carry bit, so we special case zero operands where that happens.
    IntRange computeRange(const BinaryExpression& expr) {
        auto& type = *expr.type;
        auto full = IntRange::forType(type);
        switch (expr.op) {
            case BinaryOperator::Add: {
                auto l = getSubRange(expr.left(), type);
                auto r = getSubRange(expr.right(), type);
                if (l.width == 0)
                    return r;
                if (r.width == 0)
                    return l;
                if (l.nonNegative && r.nonNegative)
                    return {std::max(l.width, r.width) + 1, true};
                return {std::max(l.signedWidth(), r.signedWidth()) + 1, false};
            }
            case BinaryOperator::Subtract: {
                auto l = getSubRange(expr.left(), type);
                auto r = getSubRange(expr.right(), type);
                if (r.width == 0)
                    return l;
                return {std::max(l.signedWidth(), r.signedWidth()) + 1, false};
            }
            case BinaryOperator::Multiply: {
                auto l = getSubRange(expr.left(), type);
                auto r = getSubRange(expr.right(), type);
                if (l.width == 0 || r.width == 0)
                    return {0, true};
                if (l.nonNegative && r.nonNegative)
                    return {l.width + r.width, true};
                return {l.signedWidth() + r.signedWidth(), false};
            }
            case BinaryOperator::Divide: {
                // The magnitude of the result can't be larger than the magnitude
                // of the dividend, except when negating the most negative value.
                auto l = getSubRange(expr.left(), type);
                auto r = getSubRange(expr.right(), type);
                if (l.nonNegative && r.nonNegative)
                    return l;
                return {l.signedWidth() + 1, false};
            }
            case BinaryOperator::Mod: {
                // The result has the sign of the dividend, and its magnitude
                // is less than both the dividend and the divisor.
                auto l = getSubRange(expr.left(), type);
                auto r = getSubRange(expr.right(), type);
                auto divisorBits = r.signedWidth() - 1;
                if (l.nonNegative)
                    return {std::min(l.width, divisorBits), true};
                return {std::min(l.width, divisorBits + 1), false};
            }
            case BinaryOperator::BinaryAnd: {
                auto l = getSubRange(expr.left(), type);
                auto r = getSubRange(expr.right(), type);
                if (l.nonNegative && r.nonNegative)
                    return {std::min(l.width, r.width), true};
                if (l.nonNegative)
                    return l;
                if (r.nonNegative)
                    return r;
                return {std::max(l.width, r.width), false};
            }
            case BinaryOperator::BinaryOr:
            case BinaryOperator::BinaryXor:
                return IntRange::join(getSubRange(expr.left(), type),
                                      getSubRange(expr.right(), type));
            case BinaryOperator::BinaryXnor: {
                // ~(a ^ b)
                auto x = IntRange::join(getSubRange(expr.left(), type),
                                        getSubRange(expr.right(), type));
                if (x.nonNegative)
                    return {x.width + 1, false};
                return x;
            }
            case BinaryOperator::Equality:
            case BinaryOperator::Inequality:
            case BinaryOperator::CaseEquality:
            case BinaryOperator::CaseInequality:
            case BinaryOperator::GreaterThanEqual:
            case BinaryOperator::GreaterThan:
            case BinaryOperator::LessThanEqual:
            case BinaryOperator::LessThan:
            case BinaryOperator::WildcardEquality:
            case BinaryOperator::WildcardInequality:
            case BinaryOperator::LogicalAnd:
            case BinaryOperator::LogicalOr:
            case BinaryOperator::LogicalImplication:
            case BinaryOperator::LogicalEquivalence:
                return {1, true};
            case BinaryOperator::LogicalShiftLeft:
            case BinaryOperator::ArithmeticShiftLeft: {
                auto l = getSubRange(expr.left(), type);
                auto amount = getShiftAmount(expr.right());
                if (l.width == 0)
                    return l;
                if (!amount)
                    return full;

                auto shift = amount->as<bitwidth_t>().value_or(type.getBitWidth());
                shift = std::min(shift, type.getBitWidth());
                return {l.width + shift, l.nonNegative};
            }
            case BinaryOperator::LogicalShiftRight:
            case BinaryOperator::ArithmeticShiftRight: {
                auto l = getSubRange(expr.left(), type);
                auto amount = getShiftAmount(expr.right());
                bool isArithmetic = expr.op == BinaryOperator::ArithmeticShiftRight &&
                                    type.isSigned();

                // A logical shift of a negative value shifts zeros
                // in on top of the full width of the type.
                if (!l.nonNegative && !isArithmetic)
                    l = {type.getBitWidth(), true};

                if (!amount)
                    return l;

                auto shift = amount->as<bitwidth_t>().value_or(type.getBitWidth());
                auto minWidth = l.nonNegative ? 0u : 1u;
                if (shift >= l.width - minWidth)
                    return {minWidth, l.nonNegative};
                return {l.width - shift, l.nonNegative};
            }
            case BinaryOperator::Power:
                return full;
        }
        SLANG_UNREACHABLE;
    }

    IntRange computeRange(const ConcatenationExpression& expr) {
        // Leading zero operands don't contribute to the range of the result,
        // and if the first operand that isn't zero is known to have its top
        // bits clear we can narrow the range based on that as well.
        auto operands = expr.operands();
        bitwidth_t result = 0;
        size_t i = 0;
        for (; i < operands.size(); i++) {
            auto& op = *operands[i];
            if (!op.type->isIntegral())
                return IntRange::forType(*expr.type);

            auto r = getRange(op);
            if (!r.nonNegative)
                break;

            if (r.width > 0) {
                result = r.width;
                i++;
                break;
            }
        }

        for (; i < operands.size(); i++) {
            if (!operands[i]->type->isIntegral())
                return IntRange::forType(*expr.type);
            result += operands[i]->type->getBitWidth();
        }

        return {result, true};
    }
};

} // namespace

void TautologicalCompare::check(AnalysisContext& context, const Symbol& rootSymbol,
                                const BinaryExpression& expr) {
    if (expr.bad())
        return;

    const bool isComparison = OpInfo::isComparison(expr.op);
    if (!isComparison) {
        switch (expr.op) {
            case BinaryOperator::LogicalAnd:
            case BinaryOperator::LogicalOr:
                break;
            case BinaryOperator::BinaryAnd:
            case BinaryOperator::BinaryOr: {
                // Bitwise operators are only interesting if they're
                // being used to combine the results of comparisons.
                auto isCompare = [](const Expression& e) {
                    auto binary = e.unwrapImplicitConversions().as_if<BinaryExpression>();
                    return binary && isNumericComparison(binary->op);
                };
                if (!isCompare(expr.left()) || !isCompare(expr.right()))
                    return;
                break;
            }
            default:
                return;
        }
    }

    // Don't warn about comparisons written inside of macro bodies; the macro
    // may be tautological for some arguments but not for others.
    if (context.isFromMacroBody(expr.opRange.start()))
        return;

    Checker checker(context, rootSymbol);
    if (isComparison)
        checker.checkComparison(expr);
    else
        checker.checkLogical(expr);
}

} // namespace slang::analysis
