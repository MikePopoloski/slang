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
    REQUIRE(someVar.getType().kind == SymbolKind::EnumType);
    const auto& et = someVar.getType().as<EnumType>();

    auto values = et.values().begin();
    CHECK(values->getValue().integer() == 0); values++;
    CHECK(values->getValue().integer() == 4); values++;
    CHECK(values->getValue().integer() == 5); values++;

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
    CHECK(!instance.lookupName("SDF", LookupLocation::before(instance.memberAt<TransparentMemberSymbol>(0))));

    const auto& foshizzle = instance.memberAt<SubroutineSymbol>(5);
    CHECK(instance.lookupName("SDF", LookupLocation::after(foshizzle)));

    // The formal argument enum should not leak into the containing scope.
    CHECK(!instance.lookupName("HELLO"));

    // Inside the function we should be able to see everything
    CHECK(foshizzle.lookupName("HELLO"));
    CHECK(foshizzle.lookupName("SDF"));
    CHECK(foshizzle.lookupName("BAR"));
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
    REQUIRE(foo.getType().kind == SymbolKind::PackedStructType);

    const auto& structType = foo.getType().as<PackedStructType>();
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
    const Type& type = f.getType().getCanonicalType();
    REQUIRE(type.kind == SymbolKind::PackedArrayType);
    REQUIRE(type.isMatching(instance.memberAt<TypeAliasType>(0).targetType.getType()));

    const Type& barType = instance.memberAt<VariableSymbol>(3).getType().getCanonicalType();
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
    const Type& type = e.getType().getCanonicalType();
    REQUIRE(type.kind == SymbolKind::EnumType);
    CHECK(type.getBitWidth() == 5);

    const Type& s1_t = instance.memberAt<VariableSymbol>(6).getType().getCanonicalType();
    CHECK(s1_t.getBitWidth() == 10);

    const auto& s2_t = instance.find<TypeAliasType>("s2_t");
    REQUIRE(s2_t.getFirstForwardDecl());
    REQUIRE(s2_t.getFirstForwardDecl()->getNextForwardDecl());
    REQUIRE(!s2_t.getFirstForwardDecl()->getNextForwardDecl()->getNextForwardDecl());

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Forwarding typedef errors") {
    auto tree = SyntaxTree::fromText(R"(
module Top;

    // These have no actual type and should error.
    typedef enum e1_t;
    typedef e2;

    // Forward declare but get the base type wrong.
    typedef struct s1_t;
    typedef s1_t;

    typedef enum { SDF } s1_t;

    typedef struct s1_t;

endmodule
)", "source");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    CHECK(instance.find("e1_t") == nullptr);
    CHECK(instance.find("e2") == nullptr);

    Diagnostics diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == DiagCode::UnresolvedForwardTypedef);
    CHECK(diags[1].code == DiagCode::UnresolvedForwardTypedef);
    CHECK(diags[2].code == DiagCode::ForwardTypedefDoesNotMatch);

    CHECK(report(diags) ==
R"(source:5:18: error: forward typedef 'e1_t' does not resolve to a data type
    typedef enum e1_t;
                 ^
source:6:13: error: forward typedef 'e2' does not resolve to a data type
    typedef e2;
            ^
source:9:20: error: forward typedef basic type 'struct' does not match declaration
    typedef struct s1_t;
                   ^
source:12:26: note: declared here
    typedef enum { SDF } s1_t;
                         ^
)");
}

TEST_CASE("Unpacked arrays") {
    auto tree = SyntaxTree::fromText(R"(
module Top(logic f[3], g, h[0:1]);

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    const auto& fType = instance.find<VariableSymbol>("f").getType();
    CHECK(fType.isUnpackedArray());
    CHECK(fType.as<UnpackedArrayType>().range == ConstantRange { 0, 2 });

    const auto& gType = instance.find<VariableSymbol>("g").getType();
    CHECK(!gType.isUnpackedArray());

    const auto& hType = instance.find<VariableSymbol>("h").getType();
    CHECK(hType.isUnpackedArray());
    CHECK(hType.as<UnpackedArrayType>().range == ConstantRange{ 0, 1 });

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid unpacked dimensions") {
    auto tree = SyntaxTree::fromText(R"(
module Top(logic f[3'b1x0],
           g[-1],
           h[9999999999999],
           i[0]);

    struct packed { logic j[3]; } foo;

endmodule
)", "source");

    Compilation compilation;
    evalModule(tree, compilation);

    Diagnostics diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == DiagCode::ValueMustNotBeUnknown);
    CHECK(diags[1].code == DiagCode::ValueMustBePositive);
    CHECK(diags[2].code == DiagCode::ValueOutOfRange);
    CHECK(diags[3].code == DiagCode::ValueMustBePositive);
    CHECK(diags[4].code == DiagCode::PackedMemberNotIntegral);

    // TODO: reporting for value out of range is bad
    // TODO: report type names correctly
    CHECK(report(diags) ==
R"(source:2:20: error: value must not have any unknown bits
module Top(logic f[3'b1x0],
                   ^~~~~~
source:3:14: error: value must be positive
           g[-1],
             ^~
source:4:14: error: 1316134911 is out of allowed range (-2147483648 to 2147483647)
           h[9999999999999],
             ^~~~~~~~~~~~~
source:5:14: error: value must be positive
           i[0]);
             ^
source:7:27: error: packed members must be of integral type (type is logic$[0:2])
    struct packed { logic j[3]; } foo;
                          ^~~~
)");
}