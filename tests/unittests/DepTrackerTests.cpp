// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include <catch2/catch_test_macros.hpp>

#include "slang/driver/DepTracker.h"
#include "slang/syntax/SyntaxTree.h"

using namespace slang;
using namespace slang::syntax;

TEST_CASE("DepTracker basic dependency tracking and pruning") {
    // Test case 1: Request only moduleB as top module
    // Should return moduleB, moduleA (dependency), but not moduleC or moduleD
    auto treeA = SyntaxTree::fromText("module moduleA; endmodule\n");
    auto treeB = SyntaxTree::fromText("module moduleB; moduleA a1(); endmodule\n");
    auto treeC = SyntaxTree::fromText("module moduleC; moduleB b1(); endmodule\n");
    auto treeD = SyntaxTree::fromText("module moduleD; /* independent */ endmodule\n");

    std::vector trees = {treeA, treeB, treeC, treeD};
    DepTracker tracker(trees);
    {

        auto result = tracker.getTreesFor({"moduleB"});

        // Should find moduleB and its dependency moduleA
        CHECK(result.deps.size() == 2);

        // Check that we have the right trees and verify topological order
        auto aPos = std::find(result.deps.begin(), result.deps.end(), treeA);
        auto bPos = std::find(result.deps.begin(), result.deps.end(), treeB);

        CHECK(aPos != result.deps.end());
        CHECK(bPos != result.deps.end());
        CHECK(aPos < bPos); // moduleA must come before moduleB

        // treeC and treeD should not be included
        CHECK(std::find(result.deps.begin(), result.deps.end(), treeC) == result.deps.end());
        CHECK(std::find(result.deps.begin(), result.deps.end(), treeD) == result.deps.end());

        // Should have no missing dependencies
        CHECK(result.missingNames.empty());
    }

    // Test case 2: Request moduleC as top module
    // Should return moduleC, moduleB, moduleA (all dependencies), but not moduleD
    {

        auto result = tracker.getTreesFor({"moduleC"});

        // Should find moduleC and its dependencies (B and A)
        CHECK(result.deps.size() == 3);

        // Check that we have the right trees and verify topological order
        auto aPos = std::find(result.deps.begin(), result.deps.end(), treeA);
        auto bPos = std::find(result.deps.begin(), result.deps.end(), treeB);
        auto cPos = std::find(result.deps.begin(), result.deps.end(), treeC);

        CHECK(aPos != result.deps.end());
        CHECK(bPos != result.deps.end());
        CHECK(cPos != result.deps.end());
        CHECK(aPos < bPos); // moduleA must come before moduleB
        CHECK(bPos < cPos); // moduleB must come before moduleC

        // treeD should not be included
        CHECK(std::find(result.deps.begin(), result.deps.end(), treeD) == result.deps.end());
    }
}

TEST_CASE("DepTracker topological sort ordering") {
    // Test complex dependency chain with proper topological ordering
    // Create dependency hierarchy: top -> mid -> (leafA, leafB)
    auto treeLeafA = SyntaxTree::fromText("module leafA; endmodule\n");
    auto treeLeafB = SyntaxTree::fromText("module leafB; endmodule\n");
    auto treeMid = SyntaxTree::fromText("module mid; leafA la(); leafB lb(); endmodule\n");
    auto treeTop = SyntaxTree::fromText("module top; mid m(); endmodule\n");

    std::vector trees = {treeLeafA, treeLeafB, treeMid, treeTop};
    DepTracker tracker(trees);

    auto result = tracker.getTreesFor({"top"});

    // Should find all 4 modules: top -> mid -> (leafA, leafB)
    CHECK(result.deps.size() == 4);

    // Verify topological ordering: dependencies must come before dependents
    auto leafAPos = std::find(result.deps.begin(), result.deps.end(), treeLeafA);
    auto leafBPos = std::find(result.deps.begin(), result.deps.end(), treeLeafB);
    auto midPos = std::find(result.deps.begin(), result.deps.end(), treeMid);
    auto topPos = std::find(result.deps.begin(), result.deps.end(), treeTop);

    CHECK(leafAPos != result.deps.end());
    CHECK(leafBPos != result.deps.end());
    CHECK(midPos != result.deps.end());
    CHECK(topPos != result.deps.end());

    // Both leaves must come before mid (dependencies before dependents)
    CHECK(leafAPos < midPos);
    CHECK(leafBPos < midPos);

    // Mid must come before top
    CHECK(midPos < topPos);
}

TEST_CASE("DepTracker circular dependency handling") {
    // Test circular dependency detection and handling
    // Create circular dependency: cycleA -> cycleB -> cycleA
    auto treeCycleA = SyntaxTree::fromText("module cycleA; cycleB cb(); endmodule\n");
    auto treeCycleB = SyntaxTree::fromText("module cycleB; cycleA ca(); endmodule\n");

    std::vector trees = {treeCycleA, treeCycleB};
    DepTracker tracker(trees);

    auto result = tracker.getTreesFor({"cycleA"});

    // Should still include both modules despite circular dependency
    CHECK(result.deps.size() == 2);

    // Check that both trees are included
    CHECK(std::find(result.deps.begin(), result.deps.end(), treeCycleA) != result.deps.end());
    CHECK(std::find(result.deps.begin(), result.deps.end(), treeCycleB) != result.deps.end());

    // Algorithm should handle the cycle gracefully without infinite loop
    CHECK(result.missingNames.empty());
}

TEST_CASE("DepTracker partial dependency tree") {
    // Test requesting only mid-level module to verify partial tree extraction
    // Create dependency hierarchy with extra unused module
    auto treeLeafA = SyntaxTree::fromText("module leafA; endmodule\n");
    auto treeLeafB = SyntaxTree::fromText("module leafB; endmodule\n");
    auto treeMid = SyntaxTree::fromText("module mid; leafA la(); leafB lb(); endmodule\n");
    auto treeTop = SyntaxTree::fromText("module top; mid m(); endmodule\n");

    std::vector trees = {treeLeafA, treeLeafB, treeMid, treeTop};
    DepTracker tracker(trees);

    auto result = tracker.getTreesFor({"mid"});

    // Should find 3 modules: mid -> (leafA, leafB), but NOT top
    CHECK(result.deps.size() == 3);

    // Check that we have the right trees and verify topological order
    auto leafAPos = std::find(result.deps.begin(), result.deps.end(), treeLeafA);
    auto leafBPos = std::find(result.deps.begin(), result.deps.end(), treeLeafB);
    auto midPos = std::find(result.deps.begin(), result.deps.end(), treeMid);

    CHECK(leafAPos != result.deps.end());
    CHECK(leafBPos != result.deps.end());
    CHECK(midPos != result.deps.end());
    CHECK(leafAPos < midPos); // leafA must come before mid
    CHECK(leafBPos < midPos); // leafB must come before mid

    // treeTop should not be included (not needed for mid)
    CHECK(std::find(result.deps.begin(), result.deps.end(), treeTop) == result.deps.end());
}

TEST_CASE("DepTracker treeToDeps internal structure") {
    // Test that the internal treeToDeps mapping is correctly populated
    auto treeA = SyntaxTree::fromText("module moduleA; endmodule\n");
    auto treeB = SyntaxTree::fromText("module moduleB; moduleA a(); endmodule\n");
    auto treeC = SyntaxTree::fromText(
        "module moduleC; moduleB b(); missingModule m(); endmodule\n");

    std::vector trees = {treeA, treeB, treeC};
    DepTracker tracker(trees);

    // Check moduleA has no dependencies
    auto depsA = tracker.treeToDeps.find(treeA);
    REQUIRE(depsA != tracker.treeToDeps.end());
    CHECK(depsA->second.deps.empty());
    CHECK(depsA->second.missingNames.empty());

    // Check moduleB depends on moduleA
    auto depsB = tracker.treeToDeps.find(treeB);
    REQUIRE(depsB != tracker.treeToDeps.end());
    CHECK(depsB->second.deps.size() == 1);
    CHECK(depsB->second.deps[0] == treeA);
    CHECK(depsB->second.missingNames.empty());

    // Check moduleC depends on moduleB and has missing dependency
    auto depsC = tracker.treeToDeps.find(treeC);
    REQUIRE(depsC != tracker.treeToDeps.end());
    CHECK(depsC->second.deps.size() == 1);
    CHECK(depsC->second.deps[0] == treeB);
    CHECK(depsC->second.missingNames.size() == 1);
    CHECK(depsC->second.missingNames[0] == "missingModule");

    // Check moduleToTree mapping
    CHECK(tracker.moduleToTree.find("moduleA")->second == treeA);
    CHECK(tracker.moduleToTree.find("moduleB")->second == treeB);
    CHECK(tracker.moduleToTree.find("moduleC")->second == treeC);
    CHECK(tracker.moduleToTree.find("missingModule") == tracker.moduleToTree.end());

    // Check missingNames mapping
    auto missingEntry = tracker.missingNames.find("missingModule");
    REQUIRE(missingEntry != tracker.missingNames.end());
    CHECK(missingEntry->second.size() == 1);
    CHECK(missingEntry->second[0] == treeC);
}

TEST_CASE("DepTracker missing dependencies") {
    // Test handling of missing dependencies
    // Create module that references non-existent module
    auto treeA = SyntaxTree::fromText("module moduleA; missingModule m(); endmodule\n");

    std::vector trees = {treeA};
    DepTracker tracker(trees);

    auto result = tracker.getTreesFor({"moduleA"});

    // Should find moduleA
    CHECK(result.deps.size() == 1);
    CHECK(result.deps[0] == treeA);

    // Should report missing dependency
    CHECK(!result.missingNames.empty());
    CHECK(std::find(result.missingNames.begin(), result.missingNames.end(), "missingModule") !=
          result.missingNames.end());
}
