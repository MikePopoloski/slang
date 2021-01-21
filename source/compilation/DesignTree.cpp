//------------------------------------------------------------------------------
// DesignTree.cpp
// Post-AST elaborated design tree
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/DesignTree.h"

#include "slang/compilation/Compilation.h"
#include "slang/symbols/ASTVisitor.h"

namespace slang {

static DesignTreeNode& buildNode(Compilation& comp, const InstanceSymbol& inst,
                                 uint32_t& hierarchyDepth);

static DesignTreeNode& buildNode(Compilation& comp, const Scope& scope, uint32_t& hierarchyDepth) {
    SmallVectorSized<const DesignTreeNode*, 8> childNodes;
    for (auto& child : scope.members()) {
        if (child.isScope())
            childNodes.append(&buildNode(comp, child.as<Scope>(), hierarchyDepth));
        else if (child.kind == SymbolKind::Instance)
            childNodes.append(&buildNode(comp, child.as<InstanceSymbol>(), hierarchyDepth));
    }

    return *comp.emplace<DesignTreeNode>(scope, childNodes.copy(comp),
                                         span<const StorageElement* const>{});
}

static DesignTreeNode& buildNode(Compilation& comp, const InstanceSymbol& inst,
                                 uint32_t& hierarchyDepth) {
    if (hierarchyDepth > comp.getOptions().maxInstanceDepth) {
        return *comp.emplace<DesignTreeNode>(inst.body, span<const DesignTreeNode* const>{},
                                             span<const StorageElement* const>{});
    }

    // If the instance body has upward names we have to clone and re-check
    // expressions for specific diagnostics. This is skipped for the first
    // instance in the list of parents because that has for sure already been
    // visited when collecting diagnostics.
    const InstanceBodySymbol* body = &inst.body;
    if (comp.hasUpwardNames(inst.body)) {
        auto parents = comp.getParentInstances(*body);
        if (parents.empty() || parents[0] != &inst)
            body = &inst.body.cloneUncached();
    }

    hierarchyDepth++;
    auto& result = buildNode(comp, *body, hierarchyDepth);
    hierarchyDepth--;

    return result;
}

DesignTreeNode& DesignTreeNode::build(Compilation& comp) {
    uint32_t hierarchyDepth = 0;
    SmallVectorSized<const DesignTreeNode*, 8> childNodes;
    for (auto inst : comp.getRoot().topInstances)
        childNodes.append(&buildNode(comp, *inst, hierarchyDepth));

    return *comp.emplace<DesignTreeNode>(comp.getRoot(), childNodes.copy(comp),
                                         span<const StorageElement* const>{});
}

} // namespace slang
