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

#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/Type.h"
#include "slang/util/Util.h"


namespace netlist {

struct BitRange {
  slang::bitwidth_t start;
  slang::bitwidth_t end;
  BitRange(size_t index) : start(index), end(index) {}
  BitRange(size_t start, size_t end) : start(start), end(end) {
    SLANG_ASSERT(start <= end);
  }
  /// Given another range, return true if it overlaps with this range.
  inline bool overlap(BitRange other) const {
      return start <= other.end && other.start <= end;
  }
  /// Given another range, return true if it is contained within this range.
  inline bool contains(BitRange other) {
      return other.start >= start && other.end <= end;
  }
  size_t size() const { return end - start; }
};

class AnalyseVariableReference {
private:
    NetlistVariableReference& node;
    NetlistVariableReference::SelectorsListType::iterator selectorsIt;

public:
    AnalyseVariableReference(NetlistVariableReference &node) :
      node(node), selectorsIt(node.selectors.begin()) {
    }

    /// Given a packed struct type, return the bit position of the named field.
    BitRange getFieldRange(const slang::ast::PackedStructType &packedStruct,
                           const std::string_view fieldName) const {
        size_t offset = 0;
        for (auto &member : packedStruct.members()) {
            auto fieldWidth = member.getDeclaredType()->getType().getBitWidth();
            if (member.name == fieldName) {
                return BitRange(offset, offset+fieldWidth);
            };
            offset += fieldWidth;;
        }
        SLANG_UNREACHABLE;
    }

    BitRange handleScalarElementSelect(const slang::ast::Type &type, BitRange range) {
        const auto& elementSelector = selectorsIt->get()->as<VariableElementSelect>();
        SLANG_ASSERT(elementSelector.getIndexInt() >= range.start);
        SLANG_ASSERT(elementSelector.getIndexInt() <= range.end);
        size_t index = range.start + elementSelector.getIndexInt();
        return BitRange(index);
    }

    BitRange handleScalarRangeSelect(const slang::ast::Type &type, BitRange range) {
        const auto& rangeSelector = selectorsIt->get()->as<VariableRangeSelect>();
        slang::bitwidth_t leftIndex = rangeSelector.getLeftIndexInt();
        slang::bitwidth_t rightIndex = rangeSelector.getRightIndexInt();
        SLANG_ASSERT(rightIndex <= leftIndex);
        SLANG_ASSERT(rightIndex >= range.start);
        SLANG_ASSERT(leftIndex <= range.end);
        auto newRange = BitRange(range.start + rightIndex,
                                 range.start + leftIndex);
        if (std::next(selectorsIt) != node.selectors.end()) {
            selectorsIt++;
            return getBitRangeImpl(type, newRange);
        } else {
            return newRange;
        }
    }

    BitRange handleArrayElementSelect(const slang::ast::Type &type, BitRange range) {
        const auto& elementSelector = selectorsIt->get()->as<VariableElementSelect>();
        slang::bitwidth_t index = elementSelector.getIndexInt();
        auto* elementType = type.getArrayElementType();
        SLANG_ASSERT((index * elementType->getBitWidth()) >= range.start);
        SLANG_ASSERT(((index + 1) * elementType->getBitWidth()) <= range.end);
        auto newRange = BitRange(range.start + (elementType->getBitWidth() * index),
                                 range.start + (elementType->getBitWidth() * (index + 1)) - 1);
        if (std::next(selectorsIt) != node.selectors.end()) {
            selectorsIt++;
            return getBitRangeImpl(*elementType, newRange);
        } else {
            return newRange;
        }
    }

    BitRange handleArrayRangeSelect(const slang::ast::Type &type, BitRange range) {
        const auto& rangeSelector = selectorsIt->get()->as<VariableRangeSelect>();
        slang::bitwidth_t leftIndex = rangeSelector.getLeftIndexInt();
        slang::bitwidth_t rightIndex = rangeSelector.getRightIndexInt();
        auto* elementType = type.getArrayElementType();
        SLANG_ASSERT(rightIndex <= leftIndex);
        SLANG_ASSERT((rightIndex * elementType->getBitWidth()) >= range.start);
        SLANG_ASSERT((leftIndex * elementType->getBitWidth()) <= range.end);
        auto newRange = BitRange(range.start + (rightIndex * elementType->getBitWidth()),
                                 range.start + (leftIndex * elementType->getBitWidth()) - 1);
        if (std::next(selectorsIt) != node.selectors.end()) {
            selectorsIt++;
            return getBitRangeImpl(type, newRange);
        } else {
            return newRange;
        }
    }

    BitRange handleStructMemberAccess(const slang::ast::Type &type, BitRange range) {
        //const auto& packedStruct = type.getCanonicalType().as<slang::ast::PackedStructType>();
        //SLANG_ASSERT(selectorsIt->get()->kind == VariableSelectorKind::MemberAccess);
        //const auto& memberAccessSelector = selectorsIt->get()->as<VariableMemberAccess>();
        //auto fieldRange = getFieldRange(packedStruct, memberAccessSelector.name);
        //SLANG_ASSERT(range.contains(fieldRange));
        //auto fieldType = packedStruct.getNameMap()[memberAccessSelector.name];
        //return getBitRange(fieldType, fieldRange.start, fieldRange.end);
        return BitRange(0);
    }

    BitRange handleUnionMemberAccess(const slang::ast::Type &type, BitRange range) {
        return BitRange(0);
    }

    BitRange handleEnumMemberAccess(const slang::ast::Type &type, BitRange range) {
        return BitRange(0);
    }

    /// Given a variable reference with zero or more selectors, determine the
    /// bit range that is accessed.
    BitRange getBitRangeImpl(const slang::ast::Type &type, BitRange range) {
        // No selectors
        if (node.selectors.empty()) {
            return BitRange(0, node.symbol.getDeclaredType()->getType().getBitWidth()-1);
        }
        // Simple vector
        if (type.isSimpleBitVector()) {
            if (selectorsIt->get()->isElementSelect()) {
                return handleScalarElementSelect(type, range);
            }
            else if (selectorsIt->get()->isRangeSelect()) {
                return handleScalarRangeSelect(type, range);
            }
            else {
                SLANG_ASSERT(0 && "unsupported scalar selector");
            }
        }
        // Packed or unpacked array
        else if (type.isArray()) {
            if (std::next(selectorsIt) != node.selectors.end() &&
                (std::next(selectorsIt)->get()->isElementSelect() ||
                 std::next(selectorsIt)->get()->isRangeSelect())) {
                // Multiple range or element selectors have only the effect of
                // the last one. Eg x[3:0][2:1] <=> x[2:1] or x[2:1][2] <=>
                // x[2].
                selectorsIt++;
                return getBitRangeImpl(type, range);
            }
            if (selectorsIt->get()->isElementSelect()) {
                return handleArrayElementSelect(type, range);
            }
            else if (selectorsIt->get()->isRangeSelect()) {
                return handleArrayRangeSelect(type, range);
            }
            else {
                SLANG_ASSERT(0 && "unsupported array selector");
            }
        }
        // Packed struct
        else if (type.isStruct() && !type.isUnpackedStruct()) {
            if (selectorsIt->get()->isMemberAccess()) {
                return handleStructMemberAccess(type, range);
            } else {
                SLANG_ASSERT(0 && "unsupported struct selector");
            }
        }
        // Packed union
        else if (type.isPackedUnion()) {
            if (selectorsIt->get()->isMemberAccess()) {
                return handleUnionMemberAccess(type, range);
            } else {
                SLANG_ASSERT(0 && "unsupported union selector");
            }
        }
        // Enum
        else if (type.isEnum()) {
            if (selectorsIt->get()->isMemberAccess()) {
                return handleEnumMemberAccess(type, range);
            } else {
                SLANG_ASSERT(0 && "unsupported enum selector");
            }
        }
        else {
            SLANG_ASSERT(0 && "unhandled type in getBitRangeImpl");
        }
    }

    /// Return a range indicating the bits of the variable that are accessed.
    BitRange getBitRange() {
      auto& variableType = node.symbol.getDeclaredType()->getType();
      return getBitRangeImpl(variableType, BitRange(0, variableType.getBitWidth()-1));
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
        return AnalyseVariableReference(sourceNode).getBitRange().overlap(
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
