#include "Test.h"

TEST_CASE("Enum declaration", "[types]") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    enum logic [3:0] {
        A,
        B = 4,
        C
    } someVar;
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    // Make sure the enum value can be looked up in the parent scope.
    CHECK(instance.find("A"));
    CHECK(instance.find("B"));
    CHECK(instance.find("C"));

    const auto& someVar = instance.memberAt<VariableSymbol>(3);
    REQUIRE(someVar.type->kind == SymbolKind::EnumType);
    const auto& et = someVar.type->as<EnumType>();

    auto values = et.values().begin();
    CHECK((*values++)->value.integer() == 0);
    CHECK((*values++)->value.integer() == 4);
    CHECK((*values++)->value.integer() == 5);

    // TODO: test (and implement) all the restrictions on enum and enum values
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Enum value leakage") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(enum { FOO, BAR } asdf = BAR) ();
    
    function enum {SDF, KJH} foshizzle(enum logic [1:0] { HELLO, GOODBYE } p);
    endfunction

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    CHECK(instance.find("FOO"));
    CHECK(instance.find("BAR"));

    // Try to look up after the parameter but before the function; should fail.
    CHECK(!instance.lookupUnqualified("SDF", LookupLocation::before(instance.memberAt<TransparentMemberSymbol>(0))));

    const auto& foshizzle = instance.memberAt<SubroutineSymbol>(5);
    CHECK(instance.lookupUnqualified("SDF", LookupLocation::after(foshizzle)));

    // The formal argument enum should not leak into the containing scope.
    CHECK(!instance.lookupUnqualified("HELLO"));

    // Inside the function we should be able to see everything
    CHECK(foshizzle.lookupUnqualified("HELLO"));
    CHECK(foshizzle.lookupUnqualified("SDF"));
    CHECK(foshizzle.lookupUnqualified("BAR"));
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Packed structs") {
    auto tree = SyntaxTree::fromText(R"(
module Top;

    struct packed {
        logic bar;
        int baz;
        logic [5:1] bif;
    } foo;

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    const auto& foo = instance.memberAt<VariableSymbol>(0);
    REQUIRE(foo.type->kind == SymbolKind::PackedStructType);

    const auto& structType = foo.type->as<PackedStructType>();
    CHECK(structType.bitWidth == 38);
    CHECK(structType.isFourState);
    CHECK(!structType.isSigned);
    CHECK(structType.isIntegral());
    CHECK(!structType.isAggregate());

    CHECK(structType.find("bar"));
    CHECK(structType.find("baz"));
    CHECK(structType.find("bif"));
    NO_COMPILATION_ERRORS;
}
