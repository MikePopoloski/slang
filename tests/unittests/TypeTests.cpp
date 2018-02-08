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
    CHECK(values->value.integer() == 0); values++;
    CHECK(values->value.integer() == 4); values++;
    CHECK(values->value.integer() == 5); values++;

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

TEST_CASE("Typedefs") {
    auto tree = SyntaxTree::fromText(R"(
module Top;

    typedef logic [3:0] foo_t;
    foo_t f;

    typedef struct packed { logic b; } bar_t;
    bar_t b;

    typedef enum { SDF, BAZ } enum_t;
    parameter enum_t e = BAZ;

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    const auto& f = instance.memberAt<VariableSymbol>(1);
    const Type& type = f.type->getCanonicalType();
    REQUIRE(type.kind == SymbolKind::PackedArrayType);
    REQUIRE(type.isMatching(*instance.memberAt<TypeAliasType>(0).targetType));

    const Type& barType = instance.memberAt<VariableSymbol>(3).type->getCanonicalType();
    CHECK(barType.getBitWidth() == 1);
    CHECK(barType.isFourState());

    CHECK(instance.memberAt<ParameterSymbol>(7).getValue().integer() == 1);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Forwarding typedefs") {
    auto tree = SyntaxTree::fromText(R"(
module Top;

    // Forward declared enum
    typedef enum e1_t;
    e1_t e1;
    typedef enum logic [4:0] { SDF, FOO } e1_t;
    
    // Forward declared struct, multiple forward declarations
    typedef struct s1_t;
    s1_t s;
    typedef struct s1_t;
    typedef s1_t;
    typedef struct packed { logic [9:0] l; } s1_t;

    // Typedef first, then forward decls
    typedef struct packed { logic r; } s2_t;
    typedef s2_t;
    typedef struct s2_t;

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    const auto& e = instance.memberAt<VariableSymbol>(1);
    const Type& type = e.type->getCanonicalType();
    REQUIRE(type.kind == SymbolKind::EnumType);
    CHECK(type.getBitWidth() == 5);

    const Type& s1_t = instance.memberAt<VariableSymbol>(6).type->getCanonicalType();
    CHECK(s1_t.getBitWidth() == 10);

    const auto& s2_t = instance.find<TypeAliasType>("s2_t");
    REQUIRE(s2_t.getFirstForwardDecl());
    REQUIRE(s2_t.getFirstForwardDecl()->getNextForwardDecl());
    REQUIRE(!s2_t.getFirstForwardDecl()->getNextForwardDecl()->getNextForwardDecl());

    NO_COMPILATION_ERRORS;
}