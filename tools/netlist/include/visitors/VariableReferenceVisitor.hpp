//------------------------------------------------------------------------------
//! @file VariableReferenceVisitor.h
//! @brief Extract variable references from expressions.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Netlist.h"

#include "slang/ast/ASTVisitor.h"

using namespace slang;

namespace netlist {

/// An AST visitor to identify variable references with selectors in
/// expressions, adding them to a visit list supplied by the caller.
class VariableReferenceVisitor : public ast::ASTVisitor<VariableReferenceVisitor, false, true> {
public:
    explicit VariableReferenceVisitor(Netlist& netlist, ast::EvalContext& evalCtx,
                                      bool leftOperand = false) :
        netlist(netlist), evalCtx(evalCtx), leftOperand(leftOperand) {}

    void handle(const ast::NamedValueExpression& expr) {

        // If the symbol reference is to a constant (eg a parameter or enum
        // value), then skip it.
        if (!expr.eval(evalCtx).bad()) {
            return;
        }

        // Add the variable reference to the netlist.
        auto& node = netlist.addVariableReference(expr.symbol, expr, leftOperand);
        varList.push_back(&node);
        for (auto* selector : selectors) {
            if (selector->kind == ast::ExpressionKind::ElementSelect) {
                const auto& expr = selector->as<ast::ElementSelectExpression>();
                auto index = expr.selector().eval(evalCtx);
                node.addElementSelect(expr, index);
            }
            else if (selector->kind == ast::ExpressionKind::RangeSelect) {
                const auto& expr = selector->as<ast::RangeSelectExpression>();
                auto leftIndex = expr.left().eval(evalCtx);
                auto rightIndex = expr.right().eval(evalCtx);
                node.addRangeSelect(expr, leftIndex, rightIndex);
            }
            else if (selector->kind == ast::ExpressionKind::MemberAccess) {
                node.addMemberAccess(selector->as<ast::MemberAccessExpression>().member.name);
            }
        }

        // Reverse the selectors.
        std::reverse(node.selectors.begin(), node.selectors.end());

        // Determine the access range to the variable.
        if (!selectors.empty()) {
            SmallVector<std::pair<const slang::ast::ValueSymbol*, const slang::ast::Expression*>>
                prefixes;
            selectors.front()->getLongestStaticPrefixes(prefixes, evalCtx);
            SLANG_ASSERT(prefixes.size() == 1);
            auto [prefixSymbol, prefixExpr] = prefixes.back();
            auto bounds = slang::ast::ValueDriver::getBounds(*prefixExpr, evalCtx,
                                                             prefixSymbol->getType());
            node.bounds = {static_cast<int32_t>(bounds->first),
                           static_cast<int32_t>(bounds->second)};
        }
        else {
            node.bounds = {0, getTypeBitWidth(expr.symbol.getType()) - 1};
        }
        DEBUG_PRINT("Variable reference: {} bounds [{}:{}]\n", node.toString(), node.bounds.upper(),
                    node.bounds.lower());

        // Clear the selectors for the next named value.
        selectors.clear();
    }

    void handle(const ast::ElementSelectExpression& expr) {
        selectors.push_back(&expr);
        expr.value().visit(*this);
    }

    void handle(const ast::RangeSelectExpression& expr) {
        selectors.push_back(&expr);
        expr.value().visit(*this);
    }

    void handle(const ast::MemberAccessExpression& expr) {
        selectors.push_back(&expr);
        expr.value().visit(*this);
    }

    std::vector<NetlistNode*>& getVars() { return varList; }

private:
    Netlist& netlist;
    ast::EvalContext& evalCtx;
    /// Whether this traversal is the target of an assignment or not.
    bool leftOperand;
    std::vector<NetlistNode*> varList;
    std::vector<const ast::Expression*> selectors;

    std::pair<size_t, size_t> getTypeBitWidthImpl(slang::ast::Type const& type) {
        size_t fixedSize = type.getBitWidth();
        if (fixedSize > 0) {
            return {1, fixedSize};
        }

        size_t multiplier = 0;
        const auto& ct = type.getCanonicalType();
        if (ct.kind == slang::ast::SymbolKind::FixedSizeUnpackedArrayType) {
            auto [multiplierElem, fixedSizeElem] = getTypeBitWidthImpl(*type.getArrayElementType());
            auto rw = ct.as<slang::ast::FixedSizeUnpackedArrayType>().range.width();
            return {multiplierElem * rw, fixedSizeElem};
        }

        SLANG_UNREACHABLE;
    }

    /// Return the bit width of a slang type, treating unpacked arrays as
    /// as if they were packed.
    int32_t getTypeBitWidth(slang::ast::Type const& type) {
        auto [multiplierElem, fixedSizeElem] = getTypeBitWidthImpl(type);
        return (int32_t)(multiplierElem * fixedSizeElem);
    }
};

} // namespace netlist
