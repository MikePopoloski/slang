// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/format.h>

#include "slang/util/IntervalMap.h"

TEST_CASE("IntervalMap -- empty map") {
    struct Foo {};
    IntervalMap<int32_t, Foo*> map;

    CHECK(map.empty());
    CHECK(map.begin() == map.begin());
    CHECK(map.end() == map.begin());
    CHECK(map.end() == map.end());

    CHECK(std::cbegin(map) == map.begin());
    CHECK(std::cend(map) == map.end());
}

TEST_CASE("IntervalMap -- small num elems in root leaf") {
    IntervalMap<int32_t, int32_t> map;
    BumpAllocator ba;
    IntervalMap<int32_t, int32_t>::Allocator alloc(ba);

    map.insert(1, 10, 1, alloc);
    map.insert(3, 7, 2, alloc);
    map.insert(2, 12, 3, alloc);
    map.insert(32, 42, 4, alloc);
    map.insert(3, 6, 5, alloc);

    auto it = map.begin();
    REQUIRE(it != map.end());
    CHECK(it.left() == 1);
    CHECK(it.right() == 10);
    CHECK(*it == 1);

    ++it;
    CHECK(it.left() == 2);
    CHECK(it.right() == 12);

    it++;
    CHECK(it.left() == 3);
    CHECK(it.right() == 6);

    it++;
    CHECK(it.left() == 3);
    CHECK(it.right() == 7);

    --it;
    CHECK(it.right() == 6);

    it--;
    CHECK(it.left() == 2);
    CHECK(*it == 3);
}
