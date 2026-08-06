// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/syntax/CSTSerializer.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/Json.h"
#include "slang/text/SourceManager.h"

TEST_CASE("CSTSerializer scopes source managers to each serialization") {
    SourceManager firstSourceManager;
    SourceManager secondSourceManager;

    // Make foreign buffer ids valid but non-expanded in the first manager so this test
    // catches misclassification instead of relying on a bounds assertion.
    for (int i = 0; i < 64; i++)
        firstSourceManager.assignText("");

    auto secondText = R"(
`define DECL logic value;
module second;
    `DECL
endmodule
)";
    auto firstTree = SyntaxTree::fromText("module first; endmodule", firstSourceManager);
    auto secondTree = SyntaxTree::fromText(secondText, secondSourceManager);

    JsonWriter writer;
    CSTSerializer serializer(writer);
    writer.startArray();
    serializer.serialize(*firstTree);
    serializer.serialize(*secondTree);
    writer.endArray();

    CHECK(contains(writer.view(), "\"fromExpansion\":true"));
}

TEST_CASE("CSTSerializer accepts a source manager for a syntax node") {
    SourceManager sourceManager;
    auto text = R"(
`define DECL logic value;
module m;
    `DECL
endmodule
)";
    auto tree = SyntaxTree::fromText(text, sourceManager);

    JsonWriter writer;
    CSTSerializer serializer(writer);
    serializer.serialize(tree->root(), &sourceManager);

    CHECK(contains(writer.view(), "\"fromExpansion\":true"));
}
