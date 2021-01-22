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

class ExpressionVisitor : public ASTVisitor<ExpressionVisitor, true, true> {
public:
};

class NodeBuilder {
public:
    NodeBuilder(Compilation& compilation) : comp(compilation) {}

    DesignTreeNode& buildNode(const InstanceSymbol& inst) {
        if (path.size() > comp.getOptions().maxInstanceDepth) {
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
            if (parents.empty() || parents[0] != &inst) {
                comp.setCurrentInstancePath(path);
                body = &inst.body.cloneUncached();
                comp.addInstance(inst, *body);
            }
        }

        path.append(&inst);
        auto& result = buildNode(*body);
        path.pop();

        return result;
    }

private:
    DesignTreeNode& buildNode(const Scope& scope) {
        SmallVectorSized<const DesignTreeNode*, 8> childNodes;
        for (auto& child : scope.members()) {
            if (child.isScope())
                childNodes.append(&buildNode(child.as<Scope>()));
            else if (child.kind == SymbolKind::Instance)
                childNodes.append(&buildNode(child.as<InstanceSymbol>()));
            else
                child.visit(ExpressionVisitor());
        }

        return *comp.emplace<DesignTreeNode>(scope, childNodes.copy(comp),
                                             span<const StorageElement* const>{});
    }

    Compilation& comp;
    SmallVectorSized<const InstanceSymbol*, 8> path;
};

DesignTreeNode& DesignTreeNode::build(Compilation& comp) {
    NodeBuilder builder(comp);
    SmallVectorSized<const DesignTreeNode*, 8> childNodes;
    for (auto inst : comp.getRoot().topInstances)
        childNodes.append(&builder.buildNode(*inst));

    return *comp.emplace<DesignTreeNode>(comp.getRoot(), childNodes.copy(comp),
                                         span<const StorageElement* const>{});
}

} // namespace slang
