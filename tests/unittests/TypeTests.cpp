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
    CHECK(instance.lookupDirect("A"));
    CHECK(instance.lookupDirect("B"));
    CHECK(instance.lookupDirect("C"));

    const auto& someVar = instance.memberAt<VariableSymbol>(3);
    REQUIRE(someVar.type->kind == SymbolKind::EnumType);
    const auto& et = someVar.type->as<EnumType>();

    auto values = et.values().begin();
    CHECK((*values++)->value.integer() == 0);
    CHECK((*values++)->value.integer() == 4);
    CHECK((*values++)->value.integer() == 5);

    // TODO: test (and implement) all the restrictions on enum and enum values
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

    CHECK(instance.lookupDirect("FOO"));
    CHECK(instance.lookupDirect("BAR"));

    // Try to look up after the parameter but before the function; should fail.
    LookupResult result;
    result.referencePoint = LookupRefPoint::before(instance.memberAt<ParameterSymbol>(0));
    instance.lookup("SDF", result);
    CHECK(result.getResultKind() == LookupResult::NotFound);

    const auto& foshizzle = instance.memberAt<SubroutineSymbol>(5);
    result.clear();
    result.referencePoint = LookupRefPoint::after(foshizzle);
    instance.lookup("SDF", result);
    CHECK(result.getResultKind() == LookupResult::Found);

    // The formal argument enum should not leak into the containing scope.
    result.clear();
    result.referencePoint = LookupRefPoint::endOfScope(instance);
    instance.lookup("HELLO", result);
    CHECK(result.getResultKind() == LookupResult::NotFound);

    // Inside the function we should be able to see everything
    result.clear();
    result.referencePoint = LookupRefPoint::endOfScope(foshizzle);
    foshizzle.lookup("HELLO", result);
    CHECK(result.getResultKind() == LookupResult::Found);

    result.clear();
    result.referencePoint = LookupRefPoint::endOfScope(foshizzle);
    foshizzle.lookup("SDF", result);
    CHECK(result.getResultKind() == LookupResult::Found);

    result.clear();
    result.referencePoint = LookupRefPoint::endOfScope(foshizzle);
    foshizzle.lookup("BAR", result);
    CHECK(result.getResultKind() == LookupResult::Found);
}