// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <catch2/matchers/catch_matchers_string.hpp>
#include <sstream>

#include "slang/util/Random.h"
#include "slang/util/ThreadPool.h"
#include "slang/util/TimeTrace.h"

using namespace Catch::Matchers;

#if __cpp_exceptions && defined(CI_BUILD) && SLANG_ASSERT_ENABLED
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
    CHECK_THAT(std::string(name), ContainsSubstring("string"));

    name = typeName<slang::ast::AssertionKind>();
    CHECK_THAT(std::string(name), ContainsSubstring("slang::ast::AssertionKind"));
}

TEST_CASE("createRandomGenerator construction") {
    // Basic construction test, not much else we can do with it.
    auto rng = createRandomGenerator<std::mt19937>();
}

TEST_CASE("TimeTrace tests") {
    TimeTrace::initialize();

    auto frob = [] {
        TimeTraceScope timeScope("Nested\nbaz"sv, ""sv);
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    };

    ThreadPool pool;
    for (int i = 0; i < 20; i++) {
        pool.pushTask([i, &frob] {
            if (i % 2 == 0) {
                TimeTraceScope timeScope("Foo\"thing"sv, std::to_string(i));
                std::this_thread::sleep_for(std::chrono::milliseconds(1));
            }
            else {
                TimeTraceScope timeScope("Foo\"thing"sv, [i] { return std::to_string(i); });
                frob();
            }
        });
    }

    pool.waitForAll();

    std::ostringstream sstr;
    TimeTrace::write(sstr);
}
