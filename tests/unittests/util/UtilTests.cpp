// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/util/Random.h"

#if __cpp_exceptions && defined(CI_BUILD)
TEST_CASE("Assertions") {
    int i = 4;
    SLANG_ASSERT(i == 4);

    CHECK_THROWS_AS([&] { SLANG_ASSERT(i == 5); }(), slang::assert::AssertionException);

    CHECK_THROWS_AS([&] { SLANG_UNREACHABLE; }(), std::logic_error);
}
#endif

TEST_CASE("TypeName test") {
    CHECK(typeName<void>() == "void");

    auto name = typeName<std::string>();
    CHECK(name.find("std::basic_string<char") != std::string::npos);

    name = typeName<slang::ast::AssertionKind>();
    CHECK(name.find("slang::ast::AssertionKind") != std::string::npos);
}

TEST_CASE("createRandomGenerator construction") {
    // Basic construction test, not much else we can do with it.
    auto rng = createRandomGenerator<std::mt19937>();
}
