#include "Test.h"

//TEST_CASE("Enum declaration", "[binding:modules]") {
//    auto tree = SyntaxTree::fromText(R"(
//module Top;
//    enum logic [3:0] {
//        A,
//        B = 4,
//        C
//    } someVar;
//endmodule
//)");
//
//    Compilation compilation;
//    const auto& instance = evalModule(tree, compilation);
//    const auto& someVar = instance.memberAt<VariableSymbol>(0);
//
//    REQUIRE(someVar.type->kind == SymbolKind::EnumType);
//    const auto& et = someVar.type->as<EnumType>();
//
//    auto values = et.values().begin();
//    CHECK((*values++)->value.integer() == 0);
//    CHECK((*values++)->value.integer() == 4);
//    CHECK((*values++)->value.integer() == 5);
//
//    // TODO: test (and implement) all the restrictions on enum and enum values
//}