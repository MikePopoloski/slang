#include "Test.h"

#include "slang/compilation/ScriptSession.h"

TEST_CASE("Enum declaration") {
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
    CHECK(values->getValue().integer() == 0);
    values++;
    CHECK(values->getValue().integer() == 4);
    values++;
    CHECK(values->getValue().integer() == 5);
    values++;

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Enum range declaration") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    enum logic [3:0] {
        A[2],
        B[3:1] = 4,
        C[9:10]
    } e1;

    enum logic [3:0] {
        D[1] = 1
    } e2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& top = compilation.getRoot().find<ModuleInstanceSymbol>("Top");
    auto get = [&](string_view name) {
        return top.find<EnumValueSymbol>(name).getValue().integer();
    };

    CHECK(get("A0") == 0);
    CHECK(get("A1") == 1);
    CHECK(get("B3") == 4);
    CHECK(get("B2") == 5);
    CHECK(get("B1") == 6);
    CHECK(get("C9") == 7);
    CHECK(get("C10") == 8);
    CHECK(get("D0") == 1);

    auto& e1 = top.find<VariableSymbol>("e1");
    CHECK(e1.getType().as<EnumType>().values().size() == 7);

    auto& e2 = top.find<VariableSymbol>("e2");
    CHECK(e2.getType().as<EnumType>().values().size() == 1);
}

TEST_CASE("Enum initializer restrictions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter logic [3:0] foo = '0;
    parameter struct packed { logic [2:0] asdf; } foo2 = '0;

    enum logic [2:0] { SDF1 = 1 + 1 } e1;           // ok
    enum logic [2:0] { SDF2 = 1'd1 + 1'd1 } e2;     // bad
    enum logic [2:0] { SDF3 = 2.0 } e3;             // bad
    enum logic [2:0] { SDF4 = foo } e4;             // ok
    enum logic [2:0] { SDF5 = foo + 1 } e5;         // ok
    enum logic [2:0] { SDF6 = foo + 1'd1 } e6;      // bad
    enum logic [2:0] { SDF7 = 1 ? foo : 1'd1 } e7;  // bad
    enum logic [2:0] { SDF8 = 1 ? foo : '1 } e8;    // ok
    enum logic [2:0] { SDF9 = foo2.asdf } e9;       // ok

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::EnumValueSizeMismatch);
    CHECK(diags[1].code == diag::ValueMustBeIntegral);
    CHECK(diags[2].code == diag::EnumValueSizeMismatch);
    CHECK(diags[3].code == diag::EnumValueSizeMismatch);
}

TEST_CASE("Enum value errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum bit [2:0] { A, B = 'x } e1;            // unknown not allowed
    enum logic [2:0] { C, D = 'x, E } e2;       // incremented 'x not allowed
    enum logic [2:0] { F, G = 3'b111, H } e3;   // overflow
    enum logic [2:0] { I = 2, J = 1, K } e4;    // reuse of value
    enum logic [2:0] { L = 2, M = 2 } e5;       // reuse of value
    enum logic [2:0] { } e6;                    // no members
    enum logic [2:0] { N[-1] } e7;              // negative range
    enum logic [2:0] { O[3:-2] } e8;            // negative range
    enum logic [2:0] { P[3:2][2] } e9;          // multidimensional
    enum logic [2:0] { Q[2] = 3'b111 } e10;     // overflow
    enum logic [2:0] { R = 'x, S[1] } e11;      // incremented 'x not allowed
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
    CHECK(diags[0].code == diag::EnumValueUnknownBits);
    CHECK(diags[1].code == diag::EnumIncrementUnknown);
    CHECK(diags[2].code == diag::EnumValueOverflow);
    CHECK(diags[3].code == diag::EnumValueDuplicate);
    CHECK(diags[4].code == diag::EnumValueDuplicate);
    CHECK(diags[5].code == diag::ExpectedDeclarator);
    CHECK(diags[6].code == diag::ValueMustBePositive);
    CHECK(diags[7].code == diag::ValueMustBePositive);
    CHECK(diags[8].code == diag::EnumRangeMultiDimensional);
    CHECK(diags[9].code == diag::EnumValueOverflow);
    CHECK(diags[10].code == diag::EnumIncrementUnknown);
}

TEST_CASE("Enum assignment exception") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    integer i;
    enum {A, B} foo;

    // Would be disallowed because 4-state 'i' forces a 4-state result.
    // We carve out an exception for this.
    initial foo = i ? A : B;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
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
    CHECK(!instance.lookupName(
        "SDF", LookupLocation::before(instance.memberAt<TransparentMemberSymbol>(0))));

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

TEST_CASE("Enum -- bad value propagation") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m #(parameter int foo)();
    enum { ASDF = foo, BAR } baz;
    I i[BAR]();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
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

TEST_CASE("Packed unions") {
    auto tree = SyntaxTree::fromText(R"(
module Top;

    union packed {
        logic [4:0] bar;
        logic [5:1] bif;
    } foo;

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    const auto& foo = instance.memberAt<VariableSymbol>(0);
    REQUIRE(foo.getType().kind == SymbolKind::PackedUnionType);

    const auto& unionType = foo.getType().as<PackedUnionType>();
    CHECK(unionType.bitWidth == 5);
    CHECK(unionType.isFourState);
    CHECK(!unionType.isSigned);
    CHECK(unionType.isIntegral());
    CHECK(!unionType.isAggregate());

    CHECK(unionType.find("bar"));
    CHECK(unionType.find("bif"));
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

    typedef logic [1:0] asdf_t [3];
    parameter asdf_t p = '{ 1, 2, 3 };

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

    auto& pVal = instance.find<ParameterSymbol>("p").getValue();
    CHECK(pVal.elements().size() == 3);
    CHECK(pVal.elements()[0].integer() == 1);
    CHECK(pVal.elements()[1].integer() == 2);
    CHECK(pVal.elements()[2].integer() == 3);

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

    // Forward declared union, multiple forward declarations
    typedef union u1_t;
    u1_t u;
    typedef union u1_t;
    typedef u1_t;
    typedef union packed { logic [9:0] l; } u1_t;

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
)",
                                     "source");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    CHECK(instance.find("e1_t") == nullptr);
    CHECK(instance.find("e2") == nullptr);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::UnresolvedForwardTypedef);
    CHECK(diags[1].code == diag::UnresolvedForwardTypedef);
    CHECK(diags[2].code == diag::ForwardTypedefDoesNotMatch);

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

TEST_CASE("Packed arrays") {
    auto tree = SyntaxTree::fromText(R"(
module Top(logic[0:3][2:1] f);

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    const auto& fType = instance.find<NetSymbol>("f").getType();
    CHECK(fType.isPackedArray());
    CHECK(fType.as<PackedArrayType>().range == ConstantRange{ 0, 3 });

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unpacked arrays") {
    auto tree = SyntaxTree::fromText(R"(
module Top(logic f[3], g, h[0:1]);

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);

    const auto& fType = instance.find<NetSymbol>("f").getType();
    CHECK(fType.isUnpackedArray());
    CHECK(fType.as<UnpackedArrayType>().range == ConstantRange{ 0, 2 });

    const auto& gType = instance.find<NetSymbol>("g").getType();
    CHECK(!gType.isUnpackedArray());

    const auto& hType = instance.find<NetSymbol>("h").getType();
    CHECK(hType.isUnpackedArray());
    CHECK(hType.as<UnpackedArrayType>().range == ConstantRange{ 0, 1 });

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid unpacked dimensions") {
    auto tree = SyntaxTree::fromText(R"(
module Top(logic f[3'b1x0],
           g[-1],
           h[72'hffffffffffffffffff],
           i[0]);

    struct packed { logic j[3]; } foo;

endmodule
)",
                                     "source");

    Compilation compilation;
    evalModule(tree, compilation);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::ValueMustNotBeUnknown);
    CHECK(diags[1].code == diag::ValueMustBePositive);
    CHECK(diags[2].code == diag::ValueOutOfRange);
    CHECK(diags[3].code == diag::ValueMustBePositive);
    CHECK(diags[4].code == diag::PackedMemberNotIntegral);

    CHECK("\n" + report(diags) == R"(
source:2:20: error: value must not have any unknown bits
module Top(logic f[3'b1x0],
                   ^~~~~~
source:3:14: error: value must be positive
           g[-1],
             ^~
source:4:14: error: 72'hffffffffffffffffff is out of allowed range (-2147483648 to 2147483647)
           h[72'hffffffffffffffffff],
             ^~~~~~~~~~~~~~~~~~~~~~
source:5:14: error: value must be positive
           i[0]);
             ^
source:7:27: error: packed members must be of integral type (type is 'unpacked array [3] of logic')
    struct packed { logic j[3]; } foo;
                          ^~~~
)");
}

TEST_CASE("Typedef AKA in diagnostics") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef struct { logic a; } asdf;
    typedef asdf blah;
    blah b;
    int i = b;

    typedef logic[3:0] test1;
    typedef test1 test2[3];
    test2 t;
    chandle j = t;
endmodule
)",
                                     "source");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    CHECK("\n" + report(diags) == R"(
source:6:11: error: value of type 'blah' (aka 'asdf') cannot be assigned to type 'int'
    int i = b;
          ^ ~
source:11:15: error: value of type 'test2' (aka 'unpacked array [3] of logic[3:0]') cannot be assigned to type 'chandle'
    chandle j = t;
              ^ ~
)");
}

TEST_CASE("Type matching") {
    std::vector<std::shared_ptr<SyntaxTree>> savedTrees;

    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto declare = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(string_view(source));
        savedTrees.push_back(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(string_view(source));
        BindContext context(scope, LookupLocation::max);
        return Expression::bind(tree->root().as<ExpressionSyntax>(), context).type;
    };

    // [6.22.1] - Matching types
    auto matching = [&](const std::string& lhs, const std::string& rhs) {
        // All matching types are also equivalent; check that here.
        auto lt = typeof(lhs);
        auto rt = typeof(rhs);
        bool result = lt->isMatching(*rt);
        if (result) {
            CHECK(result == lt->isEquivalent(*rt));
        }
        return result;
    };

    declare("typedef bit bit_t;");
    declare("typedef struct { logic l; } type1_t;");
    declare("typedef type1_t type2_t;");
    declare("typedef struct { logic l; } type3_t;");

    // a) Built-in types match themselves.
    declare("bit a;");
    declare("bit b;");
    declare("logic c;");
    declare("reg d;");
    declare("real e;");
    declare("realtime f;");
    CHECK(matching("a", "b"));
    CHECK(matching("a", "a"));
    CHECK(matching("b", "a"));
    CHECK(!matching("b", "c"));
    CHECK(matching("c", "d"));
    CHECK(matching("e", "f"));

    // b) Typedefs match their unwrapped types.
    declare("bit_t bt;");
    declare("type1_t t1;");
    declare("type2_t t2;");
    CHECK(matching("bt", "a"));
    CHECK(matching("t1", "t2"));

    // c) Anonymous enums / structs match themselves and none others.
    declare("struct packed {int A; int B;} AB1, AB2;");
    declare("struct packed {int A; int B;} AB3;");
    CHECK(matching("AB1", "AB2"));
    CHECK(!matching("AB1", "AB3"));

    // d) Typedefs for enums / structs match themselves and none others.
    declare("type1_t u1;");
    declare("type3_t u3;");
    CHECK(!matching("u1", "u3"));

    // e) Simple bit vector matches built-in types
    declare("bit signed [7:0] BYTE;");
    declare("bit signed [0:7] NOTBYTE;");
    declare("byte realByte;");
    CHECK(matching("BYTE", "realByte"));
    CHECK(!matching("NOTBYTE", "realByte"));

    // f) Matching array types
    declare("byte memBytes[256];");
    declare("bit signed [7:0] myMemBytes[256];");
    declare("logic [1:0][3:0] nibbles;");
    declare("logic [7:0] myNibbles;");
    declare("logic [3:0] fooArray;");
    declare("logic [0:3] reverseFoo;");
    CHECK(matching("memBytes", "myMemBytes"));
    CHECK(!matching("nibbles", "myNibbles"));
    CHECK(!matching("fooArray", "reverseFoo"));

    // g) Adding default signedness keyword doesn't change anything
    declare("byte signed stillRealByte;");
    declare("byte unsigned notRealByte;");
    CHECK(matching("realByte", "stillRealByte"));
    CHECK(!matching("realByte", "notRealByte"));

    // h) Types imported from packages still match.
    declare("package p; typedef logic[3:0] some_type; some_type st; endpackage");
    declare("import p::some_type;");
    declare("some_type st2;");
    CHECK(matching("p::st", "st2"));

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type equivalence") {
    std::vector<std::shared_ptr<SyntaxTree>> savedTrees;

    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto declare = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(string_view(source));
        savedTrees.push_back(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(string_view(source));
        BindContext context(scope, LookupLocation::max);
        return Expression::bind(tree->root().as<ExpressionSyntax>(), context).type;
    };

    // [6.22.2] - Equivalent types
    auto equiv = [&](const std::string& lhs, const std::string& rhs) {
        return typeof(lhs)->isEquivalent(*typeof(rhs));
    };

    // b) Anonymous enum / unpacked struct is equivalent only in same decl.
    declare("struct {int A; int B;} AB1, AB2;");
    declare("struct {int A; int B;} AB3;");
    declare("enum {eA, eB} e1, e2;");
    declare("enum {eC, eD} e3;");
    CHECK(equiv("AB1", "AB2"));
    CHECK(!equiv("AB1", "AB3"));
    CHECK(equiv("e1", "e2"));
    CHECK(!equiv("e2", "e3"));

    // c) All integral types are equivalent if they have the same signedness, four state, and bit
    // width.
    declare("bit signed [7:0] BYTE;");
    declare("struct packed signed {bit[3:0]a,b;} uint8;");
    declare("struct packed signed {logic[3:0]a,b;} uint8_4st;");
    CHECK(equiv("BYTE", "uint8"));
    CHECK(!equiv("BYTE", "uint8_4st"));

    // d) Unpacked arrays are equivalent if they have the same element type and size.
    declare("bit [9:0] A[0:5];");
    declare("bit [1:10] B[6];");
    declare("typedef bit [10:1] uint10;");
    declare("uint10 C[6:1];");
    declare("bit [10:0] D[0:5];");
    declare("bit [9:0] E[0:6];");
    CHECK(equiv("A", "B"));
    CHECK(equiv("B", "C"));
    CHECK(equiv("C", "A"));
    CHECK(!equiv("D", "A"));
    CHECK(!equiv("E", "A"));

    NO_COMPILATION_ERRORS;
}

TEST_CASE("$typename") {
    ScriptSession session;

    session.eval(R"(
typedef bit node;
node [2:0] X;
int signed Y;
package A;
    enum {A,B,C=99} X;
    typedef bit [9:1'b1] word;
endpackage : A
import A::*;
module top;
    if (1) begin : foo
        typedef struct {node A,B;} AB_t;
        AB_t AB[10];
        struct {node A,B;} bar;
    end
endmodule
)");

    auto tn = [&](auto& name) { return session.eval("$typename("s + name + ")"s).str(); };

    CHECK(tn("node") == "bit");
    CHECK(tn("X") == "bit[2:0]");
    CHECK(tn("Y") == "int");
    CHECK(tn("A::X") == "enum{A=32'sd0,B=32'sd1,C=32'sd99}A::e$1");
    CHECK(tn("A::word") == "bit[9:1]");
    CHECK(tn("top.foo.AB") == "struct{bit A;bit B;}top.foo.AB_t$[0:9]");
    CHECK(tn("top.foo.bar") == "struct{bit A;bit B;}top.foo.s$2");

    NO_SESSION_ERRORS;
}