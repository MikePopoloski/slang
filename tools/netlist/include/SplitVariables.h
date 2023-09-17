//------------------------------------------------------------------------------
//! @file SplitVariables.h
//! @brief Transform netlist variable nodes to reflect connections with
///        structured variables.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Netlist.h"
#include "fmt/color.h"
#include "fmt/format.h"
#include <utility>

#include "slang/ast/Symbol.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/Type.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/numeric/SVInt.h"
#include "slang/util/Util.h"


namespace netlist {

class AnalyseVariableReference {
private:
    NetlistVariableReference& node;
    NetlistVariableReference::SelectorsListType::iterator selectorsIt;

public:
    static AnalyseVariableReference create(NetlistVariableReference &node) {
        return AnalyseVariableReference(node);
    }

    AnalyseVariableReference(NetlistVariableReference &node) :
      node(node), selectorsIt(node.selectors.begin()) {}

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

        SLANG_ASSERT(0 && "unsupported type for getTypeBitWidth");
    }

    /// Return the bit width of a slang type, treating unpacked arrays as
    /// as if they were packed.
    int32_t getTypeBitWidth(slang::ast::Type const &type) {
       auto [multiplierElem, fixedSizeElem] =  getTypeBitWidthImpl(type);
       return (int32_t) (multiplierElem * fixedSizeElem);
    }

    /// Given a scope, return the type of the named field.
    slang::ast::Type const& getScopeFieldType(const slang::ast::Scope& scope,
                                               const std::string_view name) const {
        auto* symbol = scope.find(name);
        SLANG_ASSERT(symbol != nullptr);
        return symbol->getDeclaredType()->getType();
    }

    /// Given a packed struct type, return the bit position of the named field.
    ConstantRange getStructFieldRange(const slang::ast::PackedStructType &packedStruct,
                                      const std::string_view fieldName) const {
        int32_t offset = 0;
        for (auto &member : packedStruct.members()) {
            int32_t fieldWidth = member.getDeclaredType()->getType().getBitWidth();
            if (member.name == fieldName) {
                return {offset, offset + fieldWidth - 1};
            };
            offset += fieldWidth;
        }
        SLANG_UNREACHABLE;
    }

    /// Given a packed union type, return the bit position of the named field.
    ConstantRange getUnionFieldRange(const slang::ast::PackedUnionType &packedUnion,
                                     const std::string_view fieldName) const {
        auto* symbol = packedUnion.find(fieldName);
        SLANG_ASSERT(symbol != nullptr);
        int32_t fieldWidth = symbol->getDeclaredType()->getType().getBitWidth();
        return {0, fieldWidth - 1};
    }

    /// Given an enumeration type, return the bit position of the named field.
    ConstantRange getEnumRange(const slang::ast::EnumType& enumeration) {
        auto fieldRange = enumeration.getBitVectorRange();
        return {0, (int32_t)fieldRange.width() - 1};
    }

    /// Given an array type, return the range from which the array is indexed.
    ConstantRange getArrayRange(const slang::ast::Type &type) {
        if (type.kind == slang::ast::SymbolKind::PackedArrayType) {
            auto& arrayType = type.as<slang::ast::PackedArrayType>();
            return arrayType.range;
        }
        else if (type.kind == slang::ast::SymbolKind::FixedSizeUnpackedArrayType) {
            auto& arrayType = type.as<slang::ast::FixedSizeUnpackedArrayType>();
            return arrayType.range;
        }
        else {
          SLANG_ASSERT(0 && "unexpected array type");
        }
    }

    ConstantRange handleScalarElementSelect(const slang::ast::Type& type, ConstantRange range) {
        const auto& elementSelector = selectorsIt->get()->as<VariableElementSelect>();
        if (!elementSelector.indexIsConstant()) {
          // If the selector is not a constant, then return the whole scalar as
          // the range. No further selectors expected.
          SLANG_ASSERT(std::next(selectorsIt) == node.selectors.end());
          return {range.lower(), range.lower() + (int32_t)type.getBitWidth() - 1};
        }
        // Create a new range.
        int32_t index = range.lower() + elementSelector.getIndexInt();
        SLANG_ASSERT(range.containsPoint(index));
        return {index, index};
    }

    ConstantRange handleScalarRangeSelect(const slang::ast::Type &type, ConstantRange range) {
        const auto& rangeSelector = selectorsIt->get()->as<VariableRangeSelect>();
        int32_t rightIndex = rangeSelector.getRightIndexInt();
        int32_t leftIndex = rangeSelector.getLeftIndexInt();
        // Left and right indices must be constant.
        SLANG_ASSERT(rangeSelector.leftIndexIsConstant());
        SLANG_ASSERT(rangeSelector.rightIndexIsConstant());
        // Create a new range.
        ConstantRange newRange = {range.lower() + rightIndex,
                                  range.lower() + leftIndex};
        SLANG_ASSERT(range.contains(newRange));
        if (std::next(selectorsIt) != node.selectors.end()) {
            selectorsIt++;
            return getBitRangeImpl(type, newRange);
        } else {
            return newRange;
        }
    }

    ConstantRange handleScalarRangeSelectIncr(const slang::ast::Type &type, ConstantRange range, bool isUp) {
        const auto& rangeSelector = selectorsIt->get()->as<VariableRangeSelect>();
        if (!rangeSelector.leftIndexIsConstant()) {
          // If the selector base is not constant, then return the whole scalar
          // as the range and halt analysis of any further selectors.
          selectorsIt = node.selectors.end();
          return {range.lower(), range.lower() + (int32_t)type.getBitWidth() - 1};
        }
        // Right index must be constant.
        SLANG_ASSERT(rangeSelector.rightIndexIsConstant());
        int32_t rightIndex = rangeSelector.getRightIndexInt();
        int32_t leftIndex = rangeSelector.getLeftIndexInt();
        // Create a new range.
        auto rangeEnd = isUp ? rightIndex + leftIndex : rightIndex - leftIndex;
        ConstantRange newRange = {range.lower() + rightIndex,
                                  range.lower() + rangeEnd};
        SLANG_ASSERT(range.contains(newRange));
        if (std::next(selectorsIt) != node.selectors.end()) {
            selectorsIt++;
            return getBitRangeImpl(type, newRange);
        } else {
            return newRange;
        }
    }

    ConstantRange handleArrayElementSelect(const slang::ast::Type &type, ConstantRange range) {
        const auto& elementSelector = selectorsIt->get()->as<VariableElementSelect>();
        if (!elementSelector.indexIsConstant()) {
          // If the selector is not a constant, then return the whole scalar as
          // the range and halt analysis of any further selectors.
          selectorsIt = node.selectors.end();
          return {range.lower(), range.lower() + getTypeBitWidth(type) - 1};
        }
        int32_t index = elementSelector.getIndexInt();
        auto arrayRange = getArrayRange(type);
        SLANG_ASSERT(arrayRange.containsPoint(index));
        // Adjust for non-zero array indexing.
        index -= arrayRange.lower();
        // Create a new range.
        auto* elementType = type.getArrayElementType();
        ConstantRange newRange = {range.lower() + (index * getTypeBitWidth(*elementType)),
                                  range.lower() + ((index + 1) * getTypeBitWidth(*elementType)) - 1};
        SLANG_ASSERT(range.contains(newRange));
        if (std::next(selectorsIt) != node.selectors.end()) {
            selectorsIt++;
            return getBitRangeImpl(*elementType, newRange);
        } else {
            return newRange;
        }
    }

    ConstantRange handleArrayRangeSelect(const slang::ast::Type &type, ConstantRange range) {
        const auto& rangeSelector = selectorsIt->get()->as<VariableRangeSelect>();
        int32_t leftIndex = rangeSelector.getLeftIndexInt();
        int32_t rightIndex = rangeSelector.getRightIndexInt();
        auto arrayRange = getArrayRange(type);
        // Left and right indices must be constant.
        SLANG_ASSERT(rangeSelector.leftIndexIsConstant());
        SLANG_ASSERT(rangeSelector.rightIndexIsConstant());
        // Adjust for non-zero array indexing.
        leftIndex -= arrayRange.lower();
        rightIndex -= arrayRange.lower();
        // Create a new range.
        auto* elementType = type.getArrayElementType();
        ConstantRange newRange = {range.lower() + (rightIndex * getTypeBitWidth(*elementType)),
                                  range.lower() + ((leftIndex + 1) * getTypeBitWidth(*elementType)) - 1};
        SLANG_ASSERT(range.contains(newRange));
        if (std::next(selectorsIt) != node.selectors.end()) {
            selectorsIt++;
            return getBitRangeImpl(type, newRange);
        } else {
            return newRange;
        }
    }

    ConstantRange handleArrayRangeSelectIncr(const slang::ast::Type &type, ConstantRange range, bool isUp) {
        const auto& rangeSelector = selectorsIt->get()->as<VariableRangeSelect>();
        auto* elementType = type.getArrayElementType();
        auto arrayRange = getArrayRange(type);
        if (!rangeSelector.leftIndexIsConstant()) {
          // If the selector base is not constant, then return the whole array
          // as the range and halt analysis of any further selectors.
          selectorsIt = node.selectors.end();
          return {range.lower(),
                  range.lower() + (getTypeBitWidth(*elementType) * (int32_t)arrayRange.width()) - 1};
        }
        // Right index must be constant.
        SLANG_ASSERT(rangeSelector.rightIndexIsConstant());
        int32_t rightIndex = rangeSelector.getRightIndexInt();
        int32_t leftIndex = rangeSelector.getLeftIndexInt();
        // Adjust for non-zero array indexing.
        leftIndex -= arrayRange.lower();
        rightIndex -= arrayRange.lower();
        // Create a new range.
        ConstantRange newRange = {range.lower() + (rightIndex * getTypeBitWidth(*elementType)),
                                  range.lower() + ((leftIndex + 1) * getTypeBitWidth(*elementType)) - 1};
        SLANG_ASSERT(range.contains(newRange));
        if (std::next(selectorsIt) != node.selectors.end()) {
            selectorsIt++;
            return getBitRangeImpl(type, newRange);
        } else {
            return newRange;
        }
    }

    ConstantRange handleStructMemberAccess(const slang::ast::Type &type, ConstantRange range) {
        const auto& memberAccessSelector = selectorsIt->get()->as<VariableMemberAccess>();
        const auto& packedStruct = type.getCanonicalType().as<slang::ast::PackedStructType>();
        auto fieldRange = getStructFieldRange(packedStruct, memberAccessSelector.name);
        // Create a new range.
        ConstantRange newRange = {range.lower() + fieldRange.lower(),
                                  range.lower() + fieldRange.upper()};
        SLANG_ASSERT(range.contains(newRange));
        if (std::next(selectorsIt) != node.selectors.end()) {
          selectorsIt++;
          const auto& fieldType = getScopeFieldType(packedStruct, memberAccessSelector.name);
          return getBitRangeImpl(fieldType, fieldRange);
        } else {
          return newRange;
        }
    }

    ConstantRange handleUnionMemberAccess(const slang::ast::Type &type, ConstantRange range) {
        const auto& memberAccessSelector = selectorsIt->get()->as<VariableMemberAccess>();
        const auto& packedUnion = type.getCanonicalType().as<slang::ast::PackedUnionType>();
        auto fieldRange = getUnionFieldRange(packedUnion, memberAccessSelector.name);
        // Create a new range.
        ConstantRange newRange = {range.lower() + fieldRange.lower(),
                                  range.lower() + fieldRange.upper()};
        SLANG_ASSERT(range.contains(newRange));
        if (std::next(selectorsIt) != node.selectors.end()) {
          selectorsIt++;
          const auto& fieldType = getScopeFieldType(packedUnion, memberAccessSelector.name);
          return getBitRangeImpl(fieldType, fieldRange);
        } else {
          return newRange;
        }
    }

    ConstantRange handleEnumMemberAccess(const slang::ast::Type &type, ConstantRange range) {
        const auto& memberAccessSelector = selectorsIt->get()->as<VariableMemberAccess>();
        const auto& enumeration = type.getCanonicalType().as<slang::ast::EnumType>();
        auto fieldRange = getEnumRange(enumeration);
        // Create a new range.
        ConstantRange newRange = {range.lower() + fieldRange.lower(),
                                  range.lower() + fieldRange.upper()};
        SLANG_ASSERT(range.contains(newRange));
        if (std::next(selectorsIt) != node.selectors.end()) {
          selectorsIt++;
          const auto& fieldType = getScopeFieldType(enumeration, memberAccessSelector.name);
          return getBitRangeImpl(fieldType, fieldRange);
        } else {
          return newRange;
        }
    }

    // Multiple range selectors have only the effect of the last one.
    // Eg x[3:0][2:1] <=> x[2:1] or x[2:1][2] <=> x[2].
    inline bool ignoreSelector() {
        return selectorsIt->get()->isRangeSelect() &&
               std::next(selectorsIt) != node.selectors.end() &&
               std::next(selectorsIt)->get()->isArraySelect();
    }

    /// Given a variable reference with zero or more selectors, determine the
    /// bit range that is accessed.
    ConstantRange getBitRangeImpl(const slang::ast::Type &type, ConstantRange range) {
        // No selectors
        if (node.selectors.empty()) {
            return {0, getTypeBitWidth(node.symbol.getDeclaredType()->getType()) - 1};
        }
        // Simple vector
        if (type.isPredefinedInteger() || type.isScalar() ||
            (type.isStruct() && !type.isUnpackedStruct()) || type.isPackedUnion() ||
            type.isEnum()) {

            if (ignoreSelector()) {
                selectorsIt++;
                return getBitRangeImpl(type, range);
            }

            if (selectorsIt->get()->isElementSelect()) {
                return handleScalarElementSelect(type, range);
            }
            else if (selectorsIt->get()->isRangeSelect()) {
                switch (selectorsIt->get()->as<VariableRangeSelect>().expr.getSelectionKind()) {
                  case ast::RangeSelectionKind::Simple:
                    return handleScalarRangeSelect(type, range);
                  case ast::RangeSelectionKind::IndexedUp:
                    return handleScalarRangeSelectIncr(type, range, true);
                  case ast::RangeSelectionKind::IndexedDown:
                    return handleScalarRangeSelectIncr(type, range, false);
                  default:
                    SLANG_UNREACHABLE;
                }
            } else if (selectorsIt->get()->isMemberAccess()) {
                if (type.isStruct()) {
                    return handleStructMemberAccess(type, range);
                } else if (type.isPackedUnion()) {
                    return handleUnionMemberAccess(type, range);
                } else if (type.isEnum()) {
                    return handleEnumMemberAccess(type, range);
                } else {
                    SLANG_ASSERT(0 && "unsupported member selector");
                }
            } else {
                SLANG_ASSERT(0 && "unsupported scalar selector");
            }
        }
        // Packed or unpacked array
        else if (type.isArray()) {
            if (ignoreSelector()) {
                selectorsIt++;
                return getBitRangeImpl(type, range);
            }
            if (selectorsIt->get()->isElementSelect()) {
                return handleArrayElementSelect(type, range);
            }
            else if (selectorsIt->get()->isRangeSelect()) {
                switch (selectorsIt->get()->as<VariableRangeSelect>().expr.getSelectionKind()) {
                  case ast::RangeSelectionKind::Simple:
                    return handleArrayRangeSelect(type, range);
                  case ast::RangeSelectionKind::IndexedUp:
                    return handleArrayRangeSelectIncr(type, range, true);
                  case ast::RangeSelectionKind::IndexedDown:
                    return handleArrayRangeSelectIncr(type, range, false);
                  default:
                    SLANG_UNREACHABLE;
                }
            }
            else {
                SLANG_ASSERT(0 && "unsupported array selector");
            }
        }
        else {
            SLANG_ASSERT(0 && "unhandled type in getBitRangeImpl");
        }
    }

    /// Return a range indicating the bits of the variable that are accessed.
    ConstantRange getBitRange() {
        auto& variableType = node.symbol.getDeclaredType()->getType();
        return getBitRangeImpl(variableType, {0, getTypeBitWidth(variableType) - 1});
    }
};

/// A class to perform a transformation on the netlist to split variable
/// declaration nodes of structured types into multiple parts based on the
/// types of the incoming and outgoing edges.
class SplitVariables {
public:
    SplitVariables(Netlist& netlist) : netlist(netlist) { split(); }

private:

    /// Return true if the selection made by the target node intersects with the
    /// selection made by the source node.
    bool isIntersectingSelection(NetlistVariableReference& sourceNode,
                                 NetlistVariableReference& targetNode) const {
        return AnalyseVariableReference(sourceNode).getBitRange().overlaps(
                   AnalyseVariableReference(targetNode).getBitRange());
    }

    void split() {
        std::vector<std::tuple<NetlistVariableDeclaration*, NetlistEdge*, NetlistEdge*>>
            modifications;
        // Find each variable declaration nodes in the graph that has multiple
        // outgoing edges.
        for (auto& node : netlist) {
            if (node->kind == NodeKind::VariableDeclaration && node->outDegree() > 1) {
                auto& varDeclNode = node->as<NetlistVariableDeclaration>();
                auto& varType = varDeclNode.symbol.getDeclaredType()->getType();
                DEBUG_PRINT(fmt::format("Variable {} has type {}\n", varDeclNode.hierarchicalPath,
                                        varType.toString()));
                std::vector<NetlistEdge*> inEdges;
                netlist.getInEdgesToNode(*node, inEdges);
                // Find pairs of input and output edges that are attached to variable
                // refertence nodes. Eg.
                //   var ref -> var decl -> var ref
                // If the variable references select the same part of a structured
                // variable, then transform them into:
                //   var ref -> var alias -> var ref
                // And mark the original edges as disabled.
                for (auto* inEdge : inEdges) {
                    for (auto& outEdge : *node) {
                        if (inEdge->getSourceNode().kind == NodeKind::VariableReference &&
                            outEdge->getTargetNode().kind == NodeKind::VariableReference) {
                            auto& sourceVarRef =
                                inEdge->getSourceNode().as<NetlistVariableReference>();
                            auto& targetVarRef =
                                outEdge->getTargetNode().as<NetlistVariableReference>();
                            auto match = isIntersectingSelection(sourceVarRef, targetVarRef);
                            if (match) {
                                DEBUG_PRINT(
                                    fmt::format("New dependency through variable {} -> {}\n",
                                                sourceVarRef.toString(), targetVarRef.toString()));
                                modifications.emplace_back(&varDeclNode, inEdge, outEdge.get());
                            }
                        }
                    }
                }
            }
        }
        // Apply the operations to the graph.
        for (auto& modification : modifications) {
            auto* varDeclNode = std::get<0>(modification);
            auto* inEdge = std::get<1>(modification);
            auto* outEdge = std::get<2>(modification);
            // Disable the existing edges.
            inEdge->disable();
            outEdge->disable();
            // Create a new node that aliases the variable declaration.
            auto& varAliasNode = netlist.addVariableAlias(varDeclNode->symbol);
            // Create edges through the new node.
            inEdge->getSourceNode().addEdge(varAliasNode);
            varAliasNode.addEdge(outEdge->getTargetNode());
        }
    }

private:
    Netlist& netlist;
};

} // namespace netlist
