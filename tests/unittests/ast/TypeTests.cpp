// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/ScriptSession.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/syntax/AllSyntax.h"

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
    const auto& instance = evalModule(tree, compilation).body;

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

    auto& top = compilation.getRoot().find<InstanceSymbol>("Top").body;
    auto get = [&](std::string_view name) {
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
    CHECK(std::ranges::distance(e1.getType().as<EnumType>().values()) == 7);

    auto& e2 = top.find<VariableSymbol>("e2");
    CHECK(std::ranges::distance(e2.getType().as<EnumType>().values()) == 1);
}

TEST_CASE("Enum initializer restrictions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter logic [3:0] foo = '0;
    parameter struct packed { logic [2:0] asdf; } foo2 = '0;

    enum logic [2:0] { SDF1 = 1 + 1 } e1;           // ok
    enum logic [2:0] { SDF2 = 1'd1 } e2;            // bad
    enum logic [2:0] { SDF3 = 2.0 } e3;             // bad
    enum logic [2:0] { SDF4 = foo } e4;             // ok
    enum logic [2:0] { SDF5 = foo + 1 } e5;         // ok
    enum logic [2:0] { SDF8 = 1 ? foo : '1 } e6;    // ok
    enum logic [2:0] { SDF9 = foo2.asdf } e7;       // ok

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::EnumValueSizeMismatch);
    CHECK(diags[1].code == diag::ValueMustBeIntegral);
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
    initial foo = i != 0 ? A : B;
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
    const auto& instance = evalModule(tree, compilation).body;

    CHECK(instance.find("FOO"));
    CHECK(instance.find("BAR"));

    // Try to look up after the parameter but before the function; should fail.
    CHECK(!instance.lookupName("SDF", LookupLocation::before(
                                          instance.memberAt<TransparentMemberSymbol>(0))));

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

TEST_CASE("Enum range literal check") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam int foo = 3;
    enum { A[foo:1], B[foo] } asdf;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::EnumRangeLiteral);
    CHECK(diags[1].code == diag::EnumRangeLiteral);
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
    const auto& instance = evalModule(tree, compilation).body;

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
    const auto& instance = evalModule(tree, compilation).body;

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
    const auto& instance = evalModule(tree, compilation).body;

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
    const auto& instance = evalModule(tree, compilation).body;

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
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation).body;
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

TEST_CASE("v1800-2023: forward typedefs allowed in type operator and type param assignments") {
    auto tree = SyntaxTree::fromText(R"(
typedef C;
typedef C::T c_t;
var type(C::T) foo;
parameter type PT = C::T;

class C;
    typedef int T;
endclass
)");

    CompilationOptions options;
    options.languageVersion = LanguageVersion::v1800_2023;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Packed arrays") {
    auto tree = SyntaxTree::fromText(R"(
module Top(logic[0:3][2:1] f);

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation).body;

    const auto& fType = instance.find<NetSymbol>("f").getType();
    CHECK(fType.isPackedArray());
    CHECK(fType.as<PackedArrayType>().range == ConstantRange{0, 3});

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unpacked array ports") {
    auto tree = SyntaxTree::fromText(R"(
module Top(logic f[3], g, h[0:1]);

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation).body;

    const auto& fType = instance.find<NetSymbol>("f").getType();
    CHECK(fType.isUnpackedArray());
    CHECK(fType.as<FixedSizeUnpackedArrayType>().range == ConstantRange{0, 2});

    const auto& gType = instance.find<NetSymbol>("g").getType();
    CHECK(!gType.isUnpackedArray());

    const auto& hType = instance.find<NetSymbol>("h").getType();
    CHECK(hType.isUnpackedArray());
    CHECK(hType.as<FixedSizeUnpackedArrayType>().range == ConstantRange{0, 1});

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unpacked array kinds") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    real a[][3];
    real b[*];
    real c[int];
    real d[$];
    real e[$:9999];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& a = compilation.getRoot().lookupName<VariableSymbol>("m.a").getType();
    CHECK(a.kind == SymbolKind::DynamicArrayType);
    CHECK(a.getArrayElementType()->toString() == "real$[0:2]");

    auto& b = compilation.getRoot().lookupName<VariableSymbol>("m.b").getType();
    CHECK(b.kind == SymbolKind::AssociativeArrayType);
    CHECK(b.getArrayElementType()->toString() == "real");
    CHECK(b.getAssociativeIndexType() == nullptr);

    auto& c = compilation.getRoot().lookupName<VariableSymbol>("m.c").getType();
    CHECK(c.kind == SymbolKind::AssociativeArrayType);
    CHECK(c.getArrayElementType()->toString() == "real");
    REQUIRE(c.getAssociativeIndexType());
    CHECK(c.getAssociativeIndexType()->toString() == "int");

    auto& d = compilation.getRoot().lookupName<VariableSymbol>("m.d").getType();
    CHECK(d.kind == SymbolKind::QueueType);
    CHECK(d.getArrayElementType()->toString() == "real");
    CHECK(d.as<QueueType>().maxBound == 0);

    auto& e = compilation.getRoot().lookupName<VariableSymbol>("m.e").getType();
    CHECK(e.kind == SymbolKind::QueueType);
    CHECK(e.getArrayElementType()->toString() == "real");
    CHECK(e.as<QueueType>().maxBound == 9999);
}

TEST_CASE("Associative array -- invalid index type") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    real a[struct { int i; }];

    typedef struct { int i; } t;
    real b[t]; // this is ok

    typedef struct { real r[3][*]; } t2;
    int c[t2]; // invalid

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::CannotDeclareType);
    CHECK(diags[1].code == diag::InvalidAssociativeIndexType);
}

TEST_CASE("Invalid unpacked dimensions") {
    auto tree = SyntaxTree::fromText(R"(
module Top(logic f[3'b1x0],
           g[-1],
           h[72'hffffffffffffffffff],
           i[0]);

    struct packed { logic j[3]; } foo;

endmodule
)");

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
source:7:27: error: packed members must be of integral type (not 'unpacked array [3] of logic')
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
)");

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
        auto tree = SyntaxTree::fromText(source);
        savedTrees.push_back(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        ASTContext context(scope, LookupLocation::max);
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
    declare("logic da1[];");
    declare("bit da2[];");
    declare("logic da3[];");
    declare("bit aa1[int];");
    declare("bit aa2[*];");
    declare("bit aa3[string];");
    declare("bit aa4[int];");
    declare("logic q1[$:1];");
    declare("logic q2[$];");
    CHECK(matching("memBytes", "myMemBytes"));
    CHECK(!matching("nibbles", "myNibbles"));
    CHECK(!matching("fooArray", "reverseFoo"));
    CHECK(!matching("da1", "da2"));
    CHECK(matching("da1", "da3"));
    CHECK(!matching("da1", "myMemBytes"));
    CHECK(!matching("aa1", "aa2"));
    CHECK(!matching("aa2", "aa1"));
    CHECK(!matching("aa1", "aa3"));
    CHECK(matching("aa1", "aa4"));
    CHECK(matching("q1", "q2"));
    CHECK(!matching("q1", "da1"));

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

    // Special case for keyword integer types that have signing applied.
    declare("byte signed byteSigned2;");
    declare("byte unsigned byteUnsigned2;");
    declare("bit signed ls2;");
    declare("bit signed ls3;");
    CHECK(matching("stillRealByte", "byteSigned2"));
    CHECK(matching("byteUnsigned2", "notRealByte"));
    CHECK(matching("ls2", "ls3"));

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type equivalence") {
    std::vector<std::shared_ptr<SyntaxTree>> savedTrees;

    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto declare = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        savedTrees.push_back(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        ASTContext context(scope, LookupLocation::max);
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
    declare("bit [9:0] F[$];");
    declare("bit [1:10] G[$];");
    declare("bit [9:0] H[*];");
    declare("bit [1:10] I[int];");
    declare("bit [1:10] J[bit signed[31:0]];");
    declare("bit [1:10] K[];");
    declare("bit [9:0] L[];");
    CHECK(equiv("A", "B"));
    CHECK(equiv("B", "C"));
    CHECK(equiv("C", "A"));
    CHECK(!equiv("D", "A"));
    CHECK(!equiv("E", "A"));
    CHECK(equiv("F", "G"));
    CHECK(!equiv("F", "H"));
    CHECK(!equiv("H", "I"));
    CHECK(equiv("I", "J"));
    CHECK(equiv("K", "L"));

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assignment compatibility") {
    std::vector<std::shared_ptr<SyntaxTree>> savedTrees;

    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto declare = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        savedTrees.push_back(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        ASTContext context(scope, LookupLocation::max);
        return Expression::bind(tree->root().as<ExpressionSyntax>(), context).type;
    };

    // [6.22.3] - Assignment compatibility
    auto compat = [&](const std::string& lhs, const std::string& rhs) {
        return typeof(lhs)->isAssignmentCompatible(*typeof(rhs));
    };

    declare("bit [9:0] A[0:5];");
    declare("bit [9:0] B[$];");
    declare("bit [1:10] C[$];");
    declare("bit [9:0] D[*];");
    declare("bit [1:10] E[int];");
    declare("bit [1:10] F[];");
    declare("bit [9:0] G[];");
    CHECK(compat("A", "B"));
    CHECK(compat("B", "A"));
    CHECK(!compat("C", "D"));
    CHECK(!compat("D", "F"));
    CHECK(compat("F", "A"));
    CHECK(compat("A", "G"));
    CHECK(!compat("G", "D"));
}

TEST_CASE("$typename") {
    ScriptSession session;

    session.eval(R"(
typedef bit node;
node [2:0] X;
int signed Y;
logic [3:0][1:4] foo[$][][4][*][logic[3:0]][2:1][$:99];

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
    typedef enum{J,K} e_t;
    e_t baz;
    wire [-1:0] asdf;
endmodule
)");

    // Force the compilation to create top-level instances before we try to
    // query their names via hierarchical path.
    session.compilation.getRoot();

    auto tn = [&](auto& name) { return session.eval("$typename("s + name + ")"s).str(); };

    CHECK(tn("node") == "bit");
    CHECK(tn("X") == "bit[2:0]");
    CHECK(tn("Y") == "int");
    CHECK(tn("A::X") == "enum{A=32'sd0,B=32'sd1,C=32'sd99}A::e$1");
    CHECK(tn("A::word") == "bit[9:1]");
    CHECK(tn("top.foo.AB") == "struct{bit A;bit B;}top.foo.AB_t$[0:9]");
    CHECK(tn("top.foo.bar") == "struct{bit A;bit B;}top.foo.s$2");
    CHECK(tn("foo") == "logic[3:0][1:4]$[$][][0:3][*][logic[3:0]][2:1][$:99]");
    CHECK(tn("top.baz") == "enum{J=32'sd0,K=32'sd1}top.e_t");
    CHECK(tn("top.J") == "enum{J=32'sd0,K=32'sd1}top.e_t");
    CHECK(tn("top.asdf") == "logic[-1:0]");

    NO_SESSION_ERRORS;
}

TEST_CASE("Identical enums in different compilation units") {
    // It's expected that this should work, even though technically
    // the enums are defined in different compilation units and therefore
    // would not strictly be considered matching.
    auto tree1 = SyntaxTree::fromText(R"(
typedef enum logic [3:0] {
    A = 3, B = 7, EF = 6
} foo_t;

module m(input foo_t f);
endmodule
)");

    auto tree2 = SyntaxTree::fromText(R"(
typedef enum logic [3:0] {
    A = 3, B = 7, EF = 6
} foo_t;

module top;
    foo_t f = EF;
    m m1(.f(f));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Packed dimensions on struct / union / enum") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct packed { logic [3:0] a; int b; } [4:1] s;
    union packed { logic [3:0] a; bit [1:4] b; } [4:1] u;
    enum { A, B, C } [4:1] e;

    initial e[1] = A;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& m = compilation.getRoot().lookupName<InstanceSymbol>("m").body;
    for (auto& name : {"s"s, "u"s, "e"s}) {
        auto& type = m.find<VariableSymbol>(name).getType();
        REQUIRE(type.isPackedArray());
        CHECK(type.as<PackedArrayType>().range.upper() == 4);
    }
}

TEST_CASE("Packed array errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef logic [31:0] int_t;
    int_t [31:0][80:0][99:0][128:0] asdf;

    typedef real r_t;
    r_t [3:0] foo;

    logic [12] asdfasdf;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::PackedTypeTooLarge);
    CHECK(diags[1].code == diag::PackedArrayNotIntegral);
    CHECK(diags[2].code == diag::PackedDimsRequireFullRange);
}

TEST_CASE("Unpacked struct/union errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I; endinterface

module m;
    struct signed { int i; } s1;
    struct { int i; } [3:0] s2;
    union unsigned { int j; } u1;
    union { int i; } [3:0] u2;
    union { virtual interface I i; int j[]; } u3;
    struct tagged { int i; } s3;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::UnpackedSigned);
    CHECK(diags[1].code == diag::PackedDimsOnUnpacked);
    CHECK(diags[2].code == diag::UnpackedSigned);
    CHECK(diags[3].code == diag::PackedDimsOnUnpacked);
    CHECK(diags[4].code == diag::VirtualInterfaceUnionMember);
    CHECK(diags[5].code == diag::InvalidUnionMember);
    CHECK(diags[6].code == diag::TaggedStruct);
}

TEST_CASE("Array elements max size") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [2147483647:0] pa;
    logic ua [2147483647:0];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::PackedTypeTooLarge);
    CHECK(diags[1].code == diag::ArrayDimTooLarge);
}

TEST_CASE("Unpacked array assignment") {
    auto tree = SyntaxTree::fromText(R"(
 module test;
     localparam int a [1:0] = {1, 2};
     localparam int b [0:2] = a;
     int A[10:1];
     int C[24:1];
     assign A = C;
 endmodule
 )");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::BadAssignment);
    CHECK(diags[1].code == diag::BadAssignment);
}

TEST_CASE("Unpacked array/struct bit-streaming types") {
    auto tree = SyntaxTree::fromText(R"(
 module test;
     event a;
     localparam bits_a = $bits(a);
     event b [3:0];
     localparam bits_b = $bits(b);
     struct { event a; } c;
     localparam bits_c = $bits(c);
 endmodule
 )");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::BadSystemSubroutineArg);
    CHECK(diags[1].code == diag::BadSystemSubroutineArg);
    CHECK(diags[2].code == diag::BadSystemSubroutineArg);
}

TEST_CASE("Enum value out of range") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum logic[1:0] { a=4, b=1/0} foo1;
    enum bit signed[0:1] { c=2, d=-3} foo2;
    localparam logic [99:0] p1 = 66'b10 << 64;
    localparam logic [99:0] p2 = 66'h3;
    localparam logic [99:0] p3 = 66'hx;
    localparam logic [65:0] p4 = 66'hx;
    localparam logic [9:0] p5 = 10'bz;
    enum logic signed[3:0] { e=p1, f=p2, g=p3, h=p4, i=p5} foo3;
    localparam logic [69:0] p6 = 70'h1;
    enum bit[64:0] {j=p6} foo4;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    const int numOfErrors = 6; // a, b, c, d, e, g
    REQUIRE(diags.size() == numOfErrors);
    for (int i = 0; i < numOfErrors; i++)
        CHECK(diags[i].code == diag::EnumValueOutOfRange);
}

TEST_CASE("Virtual interface compatibility regression") {
    auto tree = SyntaxTree::fromText(R"(
class uvm_resource_db #(type T);
  static function bit read_by_name(inout T val);
    return 1;
  endfunction
endclass

interface clk_gen_if(
    output bit       valid,
    output bit       clk,
    input      [7:0] out,
    output bit [7:0] in
);
endinterface: clk_gen_if

module env;
    virtual clk_gen_if m_if;
    function void connect_phase();
        assert(uvm_resource_db#(virtual clk_gen_if)::read_by_name(m_if));
    endfunction: connect_phase
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Enum base error regress GH #414") {
    auto tree = SyntaxTree::fromText(R"(
enum DataWidth { CORE_STATUS, TEST_RESULT, WRITE_GPR } signature_type_t;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Tagged unions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef union tagged {
        struct {
            bit [4:0] reg1, reg2, regd;
        } Add;
        union tagged {
            bit [9:0] JmpU;
            struct {
                bit [1:0] cc;
                bit [9:0] addr;
            } JmpC;
        } Jmp;
        chandle baz;
        int bar[];
    } Instr;

    typedef union tagged {
        void Invalid;
        int Valid;
    } VInt;

    typedef union tagged packed {
        struct packed {
            bit [4:0] reg1, reg2, regd;
        } Add;
        union tagged packed {
            bit [9:0] JmpU;
            struct packed {
                bit [1:0] cc;
                bit [9:0] addr;
            } JmpC;
        } Jmp;
    } InstrPacked;

    typedef union tagged packed {
        void Invalid;
        int Valid;
    } VIntPacked;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Enum used in uninstantiated module -- regress") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter foo);
    typedef enum logic[foo-1:0] { A, B } et;
    int i = A;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interfaces with clocking blocks") {
    auto tree = SyntaxTree::fromText(R"(
interface SyncBus( input logic clk );
    wire a, b, c;
    clocking sb @(posedge clk);
        input a;
        output b;
        inout c;
    endclocking
endinterface

typedef virtual SyncBus VI;

task do_it( VI v );
    if( v.sb.a == 1 )
        v.sb.b <= 0;
    else
        v.sb.c <= ##1 1;
endtask

module top;
    logic clk;
    SyncBus b1( clk );
    SyncBus b2( clk );

    initial begin
        static VI v[2] = '{ b1, b2 };
        repeat( 20 )
            do_it( v[ $urandom_range( 0, 1 ) ] );
    end
endmodule

interface A_Bus( input logic clk );
    wire req, gnt;
    wire [7:0] addr, data;

    clocking sb @(posedge clk);
        input gnt;
        output req, addr;
        inout data;
        property p1; gnt ##[1:3] data; endproperty
    endclocking

    modport DUT ( input clk, req, addr,
                  output gnt,
                  inout data );

    modport STB ( clocking sb );

    modport TB ( input gnt,
                 output req, addr,
                 inout data );
endinterface

module dev1(A_Bus.DUT b);
endmodule

module dev2(A_Bus.DUT b);
endmodule

module top2;
    logic clk;
    A_Bus b1( clk );
    A_Bus b2( clk );

    dev1 d1( b1 );
    dev2 d2( b2 );

    T tb( b1, b2 );
endmodule

program T (A_Bus.STB b1, A_Bus.STB b2 );
    typedef virtual A_Bus.STB SYNCTB;

    task request( SYNCTB s );
        s.sb.req <= 1;
    endtask

    task wait_grant( SYNCTB s );
        wait( s.sb.gnt == 1 );
    endtask

    task drive(SYNCTB s, logic [7:0] adr, data );
        if( s.sb.gnt == 0 ) begin
            request(s);
            wait_grant(s);
        end

        s.sb.addr <= adr;
        s.sb.data <= data;

        repeat(2) @s.sb;
        s.sb.req <= 0;
    endtask

    typedef logic [7:0] addr_t;

    assert property (b1.sb.p1);
    initial begin
        drive( b1, addr_t'($random), addr_t'($random) );
        drive( b2, addr_t'($random), addr_t'($random) );
    end
endprogram
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interfaces with nested hierarchical names") {
    auto tree = SyntaxTree::fromText(R"(
interface clk_generator(output logic clk);
realtime period;
initial begin
    clk = 0;
    period = 0ns;
    forever begin
        if (period != 0ns) begin
            #(period/2) clk = 1;
            #(period/2) clk = 0;
        end else begin
            clk = 0;
            @(period);
        end
    end
end
endinterface

interface testbench(output logic clk_slow, output logic clk_fast);
    clk_generator bus_clk_slow(
        .clk(clk_slow)
    );
    clk_generator bus_clk_fast(
        .clk(clk_fast)
    );
endinterface

class TB;
    virtual testbench tb_intf;

    task run();
        tb_intf.bus_clk_slow.period = 10ns;
        #1us;
        tb_intf.bus_clk_fast.period = 2ns;
        #1us;
        tb_intf.bus_clk_slow.period = 0ns;
    endtask
endclass

module top;
    logic clk_100;
    logic clk_500;

    testbench testbench(
        .clk_slow (clk_100),
        .clk_fast (clk_500)
    );

    initial begin
        TB tb;
        tb = new();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Typedef + type param colon access regress GH #471") {
    auto tree = SyntaxTree::fromText(R"(
class C #(type T);
    typedef T obj_type;
    function obj_type create();
        return obj_type::type_id::create();
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("rand_mode on dynamic array regress GH #478") {
    auto tree = SyntaxTree::fromText(R"(
class r;
    rand bit v[];
    function void pre_randomize();
        v.rand_mode(0);
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("virtual interfaces in uninstantiated modules GH #481") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    virtual bus_intf _bus;
    function new(virtual bus_intf bus);
        _bus = bus;
    endfunction
    function void set_intf(virtual bus_intf bus);
        _bus = bus;
    endfunction
endclass

interface bus_intf;
endinterface

interface tb_intf(
    bus_intf bus
);
    C c;
    initial begin
        c = new(bus);
        c.set_intf(bus);
        c._bus = bus;
    end
endinterface

module top;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("virtual interfaces member access via nested member") {
    auto tree = SyntaxTree::fromText(R"(
interface clk_generator(output logic clk);
realtime period;
initial begin
    clk = 0;
    period = 0ns;
    forever begin
        if (period != 0ns) begin
            #(period/2) clk = 1;
            #(period/2) clk = 0;
        end else begin
            clk = 0;
            @(period);
        end
    end
end
endinterface

interface testbench(output logic clk_slow, output logic clk_fast);
    clk_generator bus_clk_slow(
        .clk(clk_slow)
    );
    clk_generator bus_clk_fast(
        .clk(clk_fast)
    );
endinterface

class TB;
    virtual testbench tb_intf[$];

    task run();
        foreach (tb_intf[i]) begin
            fork
                automatic int j = i;
                begin
                    tb_intf[j].bus_clk_slow.period = 10ns;
                    #1us;
                    tb_intf[j].bus_clk_fast.period = 2ns;
                    #1us;
                    tb_intf[j].bus_clk_slow.period = 0ns;
                end
             join_none
        end
        wait fork;
    endtask
endclass

module top;
    logic [1:0] clk_100;
    logic [1:0] clk_500;

    testbench testbench0(
        .clk_slow (clk_100[0]),
        .clk_fast (clk_500[0])
    );

    testbench testbench1(
        .clk_slow (clk_100[1]),
        .clk_fast (clk_500[1])
    );

    initial begin
        TB tb;
        tb = new();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid enum base regress GH #472") {
    auto tree = SyntaxTree::fromText(R"(
package pkg;
    typedef enum node [3:0] {
        IDLE    = 4'h0,
        NOTIDLE
    } CXDB_SM_t;

    typedef enum node [15:0] {
        BP_IDLE    = 16'(1<<IDLE),
        BP_NOTIDLE = 16'(1<<NOTIDLE)
    } CXDB_BP_SM_t;
endpackage

module test
import pkg::*;
#(parameter bit A = 0) ();
localparam logic [3:0] SM_IDLE = A ? BP_IDLE : IDLE;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Intermittent enum label failure GH #487") {
    auto tree = SyntaxTree::fromText(R"(
`ifdef TWOSTATE
    typedef bit node;
`else
    typedef logic node;
`endif

typedef enum node [3:0] {
    IDLE = 4'h0,
    NOTIDLE
} sm_t;

typedef enum node [15:0] {
    BP_IDLE    = 16'(1<<IDLE),
    BP_NOTIDLE = 16'(1<<NOTIDLE)
} bp_sm_t;

module top;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface assignment compatiblity error") {
    auto tree = SyntaxTree::fromText(R"(
interface A #(parameter A, B);
endinterface

module m;
    virtual A #(1,2) a1;
    virtual A #(3,4) a2;
    initial a1 = a2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadAssignment);
}

TEST_CASE("Hierarchical name in type reference") {
    auto tree = SyntaxTree::fromText(R"(
module n;
    logic [17:1] foo;
endmodule

module m;
    var type(n.foo) asdf = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::TypeRefHierarchical);
}

TEST_CASE("Virtual interface parameter resolution regress GH #510") {
    auto tree = SyntaxTree::fromText(R"(
interface I #(A=1);
endinterface

class C #(A=1);
   virtual I #(.A(A)) intf;
   function void f(virtual I #(.A(A)) ifc);
      intf = ifc;
   endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface in extern func arg regress GH #511") {
    auto tree = SyntaxTree::fromText(R"(
interface I #(int unsigned WIDTH=32, int unsigned DELAY=4);
endinterface

class C;
    extern function void set_intf(virtual I #(.WIDTH(32), .DELAY(4)) intf);
endclass

function void C::set_intf(virtual I #(.WIDTH(32), .DELAY(4)) intf);
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Subroutine ref-arg type checking") {
    auto tree = SyntaxTree::fromText(R"(
package subroutines;
    task automatic put_data (input value, ref d[$]);
        d.push_back(value);
    endtask
endpackage

module stack (input clk, input int data);
    import subroutines::*;
    int data_q[$];
    always @(posedge clk)
        put_data(data[0], data_q);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::RefTypeMismatch);
}

TEST_CASE("Struct enum member lookup") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function int foo;
        struct { enum {A,B} i; } asdf;
        asdf.i = asdf.B;
        return asdf.i;
    endfunction

    localparam int bar = foo();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("m.bar");
    CHECK(bar.getValue().integer() == 1);
}

TEST_CASE("Type compatibility not based on syntax node alone") {
    auto tree = SyntaxTree::fromText(R"(
module m #(type t);
    struct { t bar; } foo;
endmodule

module n;
    m #(int) m1();
    m #(real) m2();
    initial m1.foo = m2.foo;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadAssignment);
}

TEST_CASE("User-defined nettype resolution function errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    class C;
        function real func6(real r);
        endfunction
    endclass

    nettype baz nt1 with func1;
    nettype real nt2 with bar;
    nettype real nt3 with C;
    nettype real nt4 with func1;
    nettype real nt5 with func2;
    nettype real nt6 with func3;
    nettype real nt7 with func4;
    nettype real nt8 with func5;
    nettype real nt9 with C::func6;
    nettype real nt10 with func7;
    nettype real nt11 with func8;

    function real func1;
    endfunction

    function baz func2(real r);
    endfunction

    task func3(real r);
    endtask

    function int func4(real r);
    endfunction

    function real func5(real r);
    endfunction

    import "DPI-C" function real func7(real r);

    function real func8(real r[]);
        r[1] = 3.14;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::NotASubroutine);
    CHECK(diags[3].code == diag::NTResolveSingleArg);
    CHECK(diags[4].code == diag::NTResolveTask);
    CHECK(diags[5].code == diag::NTResolveReturn);
    CHECK(diags[6].code == diag::NTResolveSingleArg);
    CHECK(diags[7].code == diag::NTResolveClass);
    CHECK(diags[8].code == diag::NTResolveUserDef);
    CHECK(diags[9].code == diag::UndeclaredIdentifier);
    CHECK(diags[10].code == diag::NTResolveArgModify);
}

TEST_CASE("Self referential struct / union member types") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct packed { int a; logic [$bits(a)-1:0] b; logic [$bits(a)-1:0] b; } s1;
    union packed { logic [3:0] a; logic [3:0] b[$bits(a)];logic [$bits(a)-1:0] b; } u1;

    struct { int a; logic [$bits(a)-1:0] b; logic [$bits(a)-1:0] b; } s2;
    union { int a; logic [$bits(a)-1:0] b; logic [$bits(a)-1:0] b; } u2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::Redefinition);
    CHECK(diags[1].code == diag::PackedMemberNotIntegral);
    CHECK(diags[2].code == diag::Redefinition);
    CHECK(diags[3].code == diag::Redefinition);
    CHECK(diags[4].code == diag::Redefinition);
}

TEST_CASE("DPI import open array types") {
    auto tree = SyntaxTree::fromText(R"(
typedef int baz;

import "DPI-C" function void f1(logic[]);
import "DPI-C" function void f2(enum logic {A,B} [] a);
import "DPI-C" function void f3(logic a[]);
import "DPI-C" function void f4(baz [] a[][3][]);
import "DPI-C" function void f5(output baz [] a[][3][]);

module m;
    logic [3:0] a;
    logic b[2][1:-1][4];
    logic [2:0] c[][3][];
    initial begin
        f1(a);
        f2(a);
        f3(b[0][-1]);
        f4(b);
        f4(c);
        f5(b);
        f5(c);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("DPI import open array errors") {
    auto tree = SyntaxTree::fromText(R"(
typedef string baz;

import "DPI-C" function void f1(baz[] a);
import "DPI-C" function void f2(bit[][1:3]);
import "DPI-C" function void f3(bit[3:0][]);
import "DPI-C" function void f4(bit[] a [][2][]);
import "DPI-C" function void f5(event a [][2][]);

module m;
    string a;
    int b[1][2][3];
    bit c[4][5][6];
    bit d[4];
    initial begin
        f4(a);
        f4(b);
        f4(c);
        f4(d);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::PackedArrayNotIntegral);
    CHECK(diags[1].code == diag::MultiplePackedOpenArrays);
    CHECK(diags[2].code == diag::MultiplePackedOpenArrays);
    CHECK(diags[3].code == diag::InvalidDPIArgType);
    CHECK(diags[4].code == diag::BadAssignment);
    CHECK(diags[5].code == diag::BadAssignment);
    CHECK(diags[6].code == diag::BadAssignment);
}

TEST_CASE("Virtual interface examples from 25.9") {
    auto tree = SyntaxTree::fromText(R"(
interface SBus;
    logic req, grant;
    logic [7:0] addr, data;
endinterface

class SBusTransactor;
    virtual SBus bus;

    function new( virtual SBus s );
        bus = s;
    endfunction

    task request();
        bus.req <= 1'b1;
    endtask

    task wait_for_bus();
        @(posedge bus.grant);
    endtask
endclass

module devA( SBus s ); endmodule
module devB( SBus s ); endmodule

module top;
    SBus s[1:4] ();
    devA a1( s[1] );
    devB b1( s[2] );
    devA a2( s[3] );
    devB b2( s[4] );

    initial begin
        SBusTransactor t[1:4];
        t[1] = new( s[1] );
        t[2] = new( s[2] );
        t[3] = new( s[3] );
        t[4] = new( s[4] );
    end
endmodule

interface PBus #(parameter WIDTH=8);
    logic req, grant;
    logic [WIDTH-1:0] addr, data;
    modport phy(input addr, ref data);
endinterface

module top2;
    PBus #(16) p16();
    PBus #(32) p32();
    virtual PBus v8;
    virtual PBus #(35) v35;
    virtual PBus #(16) v16;
    virtual PBus #(16).phy v16_phy;
    virtual PBus #(32) v32;
    virtual PBus #(32).phy v32_phy;
    initial begin
        v16 = p16;
        v32 = p32;
        v16 = p32; // illegal – parameter values don't match
        v16 = v32; // illegal – parameter values don't match
        v16_phy = v16;
        v16 = v16_phy; // illegal assignment from selected modport to
                       // no selected modport
        v32_phy = p32;
        v32 = p32.phy; // illegal assignment from selected modport to
                       // no selected modport
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::BadAssignment);
    CHECK(diags[1].code == diag::BadAssignment);
    CHECK(diags[2].code == diag::BadAssignment);
    CHECK(diags[3].code == diag::BadAssignment);
}

TEST_CASE("Virtual interface connected to interface port") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    modport m(input i);
endinterface

module m(I.m a[3][4], I.m b, I c, I d);
    virtual I i = a;
    virtual I.m ii = a;

    virtual I arr1[3][4] = a;
    virtual I.m arr2[3][4] = a;
    virtual I.m arr3[][4] = a;

    virtual I j = a[0][1];
    virtual I.m k = a[0][1];
    virtual I.m l = a.foo;
    virtual I.m n = a[0];

    virtual I o = b;
    virtual I.m p = b;

    virtual I s = c;
    virtual I.m t = c;

    virtual I u = c.m;
    virtual I.m v = c.m;

    virtual I w = d;
    virtual I.m x = d;
endmodule

module top;
    I i [3][4]();
    m m1(i, i[0][0], i[0][0], i[0][0].m);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::BadAssignment);
    CHECK(diags[1].code == diag::BadAssignment);
    CHECK(diags[2].code == diag::BadAssignment);
    CHECK(diags[3].code == diag::BadAssignment);
    CHECK(diags[4].code == diag::InvalidModportAccess);
    CHECK(diags[5].code == diag::BadAssignment);
    CHECK(diags[6].code == diag::BadAssignment);
    CHECK(diags[7].code == diag::BadAssignment);
    CHECK(diags[8].code == diag::BadAssignment);
}

TEST_CASE("Virtual interface type restrictions") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

interface J;
  virtual I i;
endinterface

union { struct { virtual I i; } foo; } asdf;

module m(input struct { virtual I i; } foo);
  J j();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::VirtualInterfaceIfaceMember);
    CHECK(diags[1].code == diag::VirtualInterfaceUnionMember);
    CHECK(diags[2].code == diag::InvalidPortSubType);
}

TEST_CASE("Max object size tests") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [7:0] foo;
    logic [7:0] bar[];
    int baz[999999999];
    struct { logic a[2147483647]; logic [7:0] b[2147483647]; } biz;
    struct packed { logic [16777214:0] a; logic [16777214:0] b; } boz;

    initial begin
        $display(foo[2147483647:1]);
        $display(bar[-2147483647:2147483647]);
    end
endmodule

class C;
    logic a[2147483647];
    logic [7:0] b[2147483647];
endclass

class D;
    int foo[9999999];
endclass

module n;
    D d[1000];
    struct { int a; D d; } asdf [1000];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::ObjectTooLarge);
    CHECK(diags[1].code == diag::ObjectTooLarge);
    CHECK(diags[2].code == diag::PackedTypeTooLarge);
    CHECK(diags[3].code == diag::RangeOOB);
    CHECK(diags[4].code == diag::PackedTypeTooLarge);
    CHECK(diags[5].code == diag::ObjectTooLarge);
    CHECK(diags[6].code == diag::ObjectTooLarge);
    CHECK(diags[7].code == diag::ObjectTooLarge);
    CHECK(diags[8].code == diag::ObjectTooLarge);
}

TEST_CASE("Giant string literal overflow") {
    std::string source = R"(
module m;
    parameter p = ")";

    source += std::string(2100000, 'A');
    source += R"(";
endmodule
)";

    auto tree = SyntaxTree::fromText(source);

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::PackedTypeTooLarge);
}

TEST_CASE("Struct implicit conversion warning regress") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type t = struct packed { logic l; })(input t t1);
endmodule

module top;
    struct packed { logic signed l; } t;
    m m1(t);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ImplicitConvert);
}

TEST_CASE("No implicit conv warning for identical structs") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct packed { logic a; } s1;
    struct packed { logic a; } s2;
    struct packed { logic b; } s3;

    assign s1 = s2;
    assign s2 = s3;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ImplicitConvert);
}

TEST_CASE("Implicit string conversion compat flag") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    string strValue;
    integer intValue;
    initial begin
        intValue = strValue;
    end
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::RelaxStringConversions;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Forward typedef restriction regress") {
    auto tree = SyntaxTree::fromText(R"(
typedef struct s;

typedef int s;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ForwardTypedefDoesNotMatch);
}

TEST_CASE("Unbounded literals can only be converted to simple bit vector types") {
    auto tree = SyntaxTree::fromText(R"(
parameter real r = $;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadAssignment);
}

TEST_CASE("v1800-2023: Soft packed unions") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
function automatic logic[7:0] foo;
    union soft { logic [7:0] a; logic [5:0] b; } u;
    u.a = 8'hff;
    u.b = 6'd0;
    return u;
endfunction

module m;
    localparam p = foo();
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type dimension overflow regress") {
    auto tree = SyntaxTree::fromText(R"(
logic [-2147483648:-2147483649] a;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::PackedTypeTooLarge);
    CHECK(diags[1].code == diag::SignedIntegerOverflow);
    CHECK(diags[2].code == diag::SignedIntegerOverflow);
}

TEST_CASE("Virtual interface element select of member") {
    auto tree = SyntaxTree::fromText(R"(
    interface iface;
        logic [255:0] data[2048];
        logic [255:0] data_3d[2048][128][128];
    endinterface

    class cls1;
        virtual iface vif;
    endclass

    class cls2;
        cls1 c;
        logic [255:0] data;
        function set(int idx);
            c.vif.data[idx] = data;
            c.vif.data_3d[idx][64][8] = data;
            c.vif.data_3d[idx][64][8][10:0] = data[10:0]; // index + range select
        endfunction
    endclass

    module top;
    endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Hierarchy-dependent type equivalence") {
    auto tree = SyntaxTree::fromText(R"(
    interface iface #(parameter int WIDTH = 1)();
        typedef struct packed {
            bit [3:0] op;
        } t;
        t [WIDTH-1:0] ready;
    endinterface

    module top();
        iface #(.WIDTH(1)) if1();
        iface #(.WIDTH(2)) if2();
    endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    auto& type1 = root.lookupName<VariableSymbol>("top.if1.ready").getType();
    auto& type2 = root.lookupName<VariableSymbol>("top.if2.ready").getType();

    CHECK(!type1.isEquivalent(type2));
}

TEST_CASE("More enum member lookup cases") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter enum {Q,R} p1 = Q, int p2 = $bits(enum{S,T}));
    initial randsequence () enum {A,B} foo : { int i = A; }; endsequence
    initial for (enum {A,B} f = A; f != B; f = B) begin automatic int i = B; end
    localparam int q = $bits(enum{A,B}) + $bits(enum{C,D});
    localparam r = B;
    localparam type s = type(B);
    localparam t = R;
    localparam u = T;
endmodule

module n #(type T = enum {U,V}, parameter p = U)(input enum {A,B} i = A,
            output int o = $bits(enum {C,D}), q = C);
    int a[] = '{U, A, C};
endmodule

checker c (enum {A,B} test_sig = A);
    a1: assert property (B);
endchecker

property p(enum {A,B} a = A);
    B;
endproperty

module o;
    int i,j;
    initial i = $bits(enum{A,B});
    assign j = $bits(enum{C,D});

    localparam p = A;
    localparam q = C;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Enum mismatch corner cases") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    extern function enum {B,C} f(enum {D,E} p, int i = $bits(enum {F}));
endclass

function enum {B,C} A::f(enum {D,E} p, int i = $bits(enum {F}));
    int j[] = '{B, D, F};
endfunction

interface I;
    modport m(import function enum{A,B} foo(enum{C,D} a = C,
              int i = $bits(enum{E,F}), int j = B));

    function automatic enum{A,B} foo(enum{C,D} a = C,
                                     int i = $bits(enum{E,F}),
                                     int j = B);
        int q[] = '{A, C, E};
    endfunction
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MethodArgTypeMismatch);
    CHECK(diags[1].code == diag::MethodReturnMismatch);
}

TEST_CASE("Enum lookup location corner cases") {
    auto tree = SyntaxTree::fromText(R"(
localparam int A = 1;
module m(input int a = C, enum {C,D} c);
    localparam int q = A + $bits(enum{A=4,B});
    localparam int r = A;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UsedBeforeDeclared);

    auto& root = compilation.getRoot();
    auto& q = root.lookupName<ParameterSymbol>("m.q");
    CHECK(q.getValue().integer() == 33);

    auto& r = root.lookupName<ParameterSymbol>("m.r");
    CHECK(r.getValue().integer() == 4);
}

TEST_CASE("Recursive typedef regress") {
    auto tree = SyntaxTree::fromText(R"(
module test;
 typedef T1;
 typedef T1 T2;
 typedef T2 T3;
 typedef T3 T1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::RecursiveDefinition);
}
