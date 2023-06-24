// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#define CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS

#include "Test.h"
#include <fmt/format.h>
#include <random>

#include "slang/util/IntervalMap.h"
#include "slang/util/Random.h"

TEST_CASE("IntervalMap -- empty map") {
    struct Foo {};
    IntervalMap<int32_t, Foo*> map;

    CHECK(map.empty());
    CHECK(map.begin() == map.begin());
    CHECK(map.end() == map.begin());
    CHECK(map.end() == map.end());
    CHECK(!map.begin().valid());

    CHECK(std::cbegin(map) == map.begin());
    CHECK(std::cend(map) == map.end());
    map.verify();
}

TEST_CASE("IntervalMap -- small num elems in root leaf") {
    IntervalMap<int32_t, int32_t> map;
    BumpAllocator ba;
    IntervalMap<int32_t, int32_t>::allocator_type alloc(ba);

    map.insert(1, 10, 1, alloc);
    map.insert(3, 7, 2, alloc);
    map.insert(2, 12, 3, alloc);
    map.insert(32, 42, 4, alloc);
    map.insert(3, 6, 5, alloc);

    auto it = map.begin();
    REQUIRE(it != map.end());
    CHECK(it.bounds() == std::pair{1, 10});
    CHECK(*it == 1);

    ++it;
    CHECK(it.bounds() == std::pair{2, 12});

    it++;
    CHECK(it.bounds() == std::pair{3, 6});

    it++;
    CHECK(it.bounds() == std::pair{3, 7});

    --it;
    CHECK(it.bounds() == std::pair{3, 6});

    it--;
    CHECK(it.bounds() == std::pair{2, 12});
    CHECK(*it == 3);

    CHECK(map.getBounds() == std::pair{1, 42});
    map.verify();

    auto oit = map.find(7, 20);
    CHECK(oit.valid());
    CHECK(oit.bounds() == std::pair{1, 10});
    CHECK(*oit == 1);

    oit++;
    CHECK(oit.valid());
    CHECK(oit.bounds() == std::pair{2, 12});

    ++oit;
    CHECK(oit.bounds() == std::pair{3, 7});

    ++oit;
    CHECK(oit == map.end());
}

TEST_CASE("IntervalMap -- branching inserts") {
    IntervalMap<int32_t, int32_t> map;
    BumpAllocator ba;
    IntervalMap<int32_t, int32_t>::allocator_type alloc(ba);

    using Int32 = std::tuple<int32_t, int32_t, int32_t>;
    std::vector<Int32> expectedOverlap;

    // A wrapper around insert that catches all intervals that would
    // overlap the test interval we check at the end of the function.
    auto insert = [&](int32_t l, int32_t r, int32_t i) {
        if (r >= 200 && l <= 250)
            expectedOverlap.push_back({l, r, i});
        map.insert(l, r, i, alloc);
    };

    // Insert a bunch of elements to force branching.
    for (int32_t i = 1; i < 1000; i++) {
        insert(10 * i, 10 * i + 5, i);
        CHECK(map.getBounds() == std::pair{10, 10 * i + 5});
    }

    CHECK(!map.empty());
    CHECK(map.getBounds() == std::pair{10, 9995});

    auto it = map.begin();
    for (int32_t i = 1; i < 1000; i++) {
        CHECK(it.valid());
        CHECK(it.bounds() == std::pair{10 * i, 10 * i + 5});
        CHECK(*it == i);
        it++;
    }

    CHECK(!it.valid());
    CHECK(it == map.end());

    for (int32_t i = 999; i; --i) {
        --it;
        CHECK(it.valid());
        CHECK(it.bounds() == std::pair{10 * i, 10 * i + 5});
        CHECK(*it == i);
    }
    CHECK(it == map.begin());

    // Insert more intervals in the middle.
    for (int32_t i = 0; i < 100; i++)
        insert(11 * i, 11 * i + i, i);

    // Insert a bunch of psuedo-random intervals.
    std::mt19937 mt;
    for (int32_t i = 0; i < 1000; i++) {
        int32_t left = getUniformIntDist(mt, 1, 10000);
        int32_t right = getUniformIntDist(mt, left, 10000);
        insert(left, right, i);
    }

    map.verify();

    // Do some overlap finds.
    std::vector<Int32> actualOverlaps;
    for (auto oit = map.find(200, 250); oit != map.end(); oit++)
        actualOverlaps.push_back({oit.bounds().first, oit.bounds().second, *oit});

    auto sorter = [](const Int32& left, const Int32& right) {
        auto ll = std::get<0>(left);
        auto rl = std::get<0>(right);
        return ll < rl || (ll == rl && std::get<1>(left) < std::get<1>(right));
    };

    std::ranges::sort(expectedOverlap, sorter);
    std::ranges::sort(actualOverlaps, sorter);

    CHECK(expectedOverlap == actualOverlaps);

    // Make sure find() within the tree that doesn't actually overlap works correctly.
    auto oit = map.find(1, 3);
    CHECK(oit == map.end());

    map.clear(alloc);
    CHECK(map.empty());
}

TEST_CASE("IntervalMap -- unioning intervals") {
    IntervalMap<int32_t, int32_t> map;
    BumpAllocator ba;
    IntervalMap<int32_t, int32_t>::allocator_type alloc(ba);

    map.unionWith({20, 30}, 1, alloc);
    map.unionWith({10, 15}, 1, alloc);
    map.unionWith({1, 2}, 1, alloc);
    map.unionWith({90, 102}, 1, alloc);
    CHECK(std::ranges::distance(map.begin(), map.end()) == 4);

    map.unionWith({3, 19}, 1, alloc);
    CHECK(std::ranges::distance(map.begin(), map.end()) == 2);

    map.unionWith({3, 8}, 1, alloc);
    map.unionWith({3, 7}, 1, alloc);
    CHECK(std::ranges::distance(map.begin(), map.end()) == 2);

    map.insert({4, 39}, 1, alloc);
    map.insert({4, 39}, 1, alloc);
    map.insert({4, 39}, 1, alloc);
    map.insert({1, 30}, 1, alloc);
    CHECK(std::ranges::distance(map.begin(), map.end()) == 6);

    map.unionWith({0, 1}, 1, alloc);
    CHECK(std::ranges::distance(map.begin(), map.end()) == 2);

    for (int i = 0; i < 16; i++)
        map.unionWith({45 + 10 * i, 50 + 10 * i}, 1, alloc);
    CHECK(std::ranges::distance(map.begin(), map.end()) == 16);

    map.unionWith({41, 42}, 1, alloc);
    map.unionWith({201, 250}, 1, alloc);
    map.unionWith({260, 300}, 1, alloc);
    CHECK(std::ranges::distance(map.begin(), map.end()) == 18);

    map.unionWith({122, 123}, 1, alloc);
    map.verify();

    // This will trigger an erase of a full branch node and collapse back to root
    map.unionWith({119, 400}, 1, alloc);
    map.verify();
    CHECK(std::ranges::distance(map.begin(), map.end()) == 9);

    for (int i = 0; i < 100; i++)
        map.unionWith({450 + 100 * i, 500 + 100 * i}, 1, alloc);

    // Union the whole map down to one element.
    map.unionWith({1, 11000}, 1, alloc);
    CHECK(std::ranges::distance(map.begin(), map.end()) == 1);
    map.verify();
}

TEST_CASE("IntervalMap -- pseudorandom union testing") {
    IntervalMap<int32_t, int32_t> map;
    BumpAllocator ba;
    IntervalMap<int32_t, int32_t>::allocator_type alloc(ba);

    // Insert a bunch of psuedo-random intervals.
    std::mt19937 mt;
    for (int32_t i = 0; i < 1000; i++) {
        int32_t left = getUniformIntDist(mt, 1, 1000);
        int32_t right = left + 2;
        map.unionWith(left, right, 1, alloc);
        map.verify();
    }

    CHECK(std::ranges::distance(map.begin(), map.end()) == 34);
}
