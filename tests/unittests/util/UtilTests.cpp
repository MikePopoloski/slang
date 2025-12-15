// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <BS_thread_pool.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>
#include <sstream>

#include "slang/util/Bag.h"
#include "slang/util/Random.h"
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

TEST_CASE("Bag constructor doesn't accept Bag") {
    // The variadic constructor has a requires clause that prevents passing a Bag
    // as an argument. Without this constraint, Bag(bag) would call set(Bag&&),
    // storing the entire Bag as an element inside itself. That would call another bag copy, which
    // would recurse infinitely and overflow the stack.

    slang::Bag bag1;
    bag1.set(42);
    bag1.set(std::string("hello"));

    // This should not compile (prevented by requires clause):
    // slang::Bag bag2(bag1);

    // Verify that the normal constructor and copy work as expected
    slang::Bag bag2(42, std::string("world"));
    CHECK(bag2.get<int>() != nullptr);
    CHECK(*bag2.get<int>() == 42);
    CHECK(bag2.get<std::string>() != nullptr);
    CHECK(*bag2.get<std::string>() == "world");

    // Copy constructor instead of bag of bag of bag of ...
    slang::Bag bag3 = bag2;
    CHECK(bag3.get<int>() != nullptr);
    CHECK(*bag3.get<int>() == 42);
}

#if defined(SLANG_USE_THREADS)

TEST_CASE("TimeTrace tests") {
    TimeTrace::initialize();

    auto frob = [] {
        TimeTraceScope timeScope("Nested\nbaz"sv, ""sv);
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    };

    BS::thread_pool pool;
    for (int i = 0; i < 20; i++) {
        pool.detach_task([i, &frob] {
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

    pool.wait();

    std::ostringstream sstr;
    TimeTrace::write(sstr);

    TimeTrace::destroy();
}

#endif
