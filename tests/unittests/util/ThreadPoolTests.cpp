// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/util/ThreadPool.h"

TEST_CASE("ThreadPool - constructor") {
    ThreadPool pool;
    CHECK(pool.getThreadCount() == std::thread::hardware_concurrency());
}

// A class to detect when a copy or move constructor has been invoked.
class DetectCopyMove {
public:
    bool copied = false;
    bool moved = false;

    DetectCopyMove() = default;
    DetectCopyMove(const DetectCopyMove&) { copied = true; }
    DetectCopyMove(DetectCopyMove&&) { moved = true; }
};

TEST_CASE("ThreadPool -- pushTask") {
    ThreadPool pool;
    {
        bool flag = false;
        pool.pushTask([&flag] { flag = true; });
        pool.waitForAll();
        CHECK(flag);
    }
    {
        bool flag = false;
        pool.pushTask([](bool* flag_) { *flag_ = true; }, &flag);
        pool.waitForAll();
        CHECK(flag);
    }
    {
        bool flag1 = false;
        bool flag2 = false;
        pool.pushTask([](bool* flag1_, bool* flag2_) { *flag1_ = *flag2_ = true; }, &flag1, &flag2);
        pool.waitForAll();
        CHECK((flag1 && flag2));
    }
    {
        // No unecessary copies of the function args.
        bool copied = false;
        bool moved = false;
        pool.pushTask([detect = DetectCopyMove(), &copied, &moved] {
            copied = detect.copied;
            moved = detect.moved;
        });
        pool.waitForAll();
        CHECK((!copied && moved));
    }
    {
        int64_t pass_me_by_value = 0;
        pool.pushTask(
            [](int64_t passed_by_value) {
                if (++passed_by_value)
                    std::this_thread::yield();
            },
            pass_me_by_value);
        pool.waitForAll();
        CHECK(pass_me_by_value == 0);

        int64_t pass_me_by_ref = 0;
        pool.pushTask([](int64_t& passed_by_ref) { ++passed_by_ref; }, std::ref(pass_me_by_ref));
        pool.waitForAll();
        CHECK(pass_me_by_ref == 1);

        int64_t pass_me_by_cref = 0;
        std::atomic<bool> release = false;
        pool.pushTask(
            [&release](const int64_t& passed_by_cref) {
                while (!release)
                    std::this_thread::yield();
                CHECK(passed_by_cref == 1);
            },
            std::cref(pass_me_by_cref));

        std::this_thread::sleep_for(std::chrono::milliseconds(10));
        ++pass_me_by_cref;
        release = true;
        pool.waitForAll();
    }
}

TEST_CASE("ThreadPool -- submit") {
    ThreadPool pool;
    {
        bool flag = false;
        pool.submit([&flag] { flag = true; }).wait();
        CHECK(flag);
    }
    {
        bool flag = false;
        pool.submit([](bool* flag_) { *flag_ = true; }, &flag).wait();
        CHECK(flag);
    }
    {
        bool flag1 = false;
        bool flag2 = false;
        pool.submit([](bool* flag1_, bool* flag2_) { *flag1_ = *flag2_ = true; }, &flag1, &flag2)
            .wait();
        CHECK((flag1 && flag2));
    }
    {
        bool flag = false;
        std::future<int> flag_future = pool.submit([&flag] {
            flag = true;
            return 42;
        });
        CHECK((flag_future.get() == 42 && flag));
    }
    {
        bool flag = false;
        std::future<int> flag_future = pool.submit(
            [](bool* flag_) {
                *flag_ = true;
                return 42;
            },
            &flag);
        CHECK((flag_future.get() == 42 && flag));
    }
    {
        bool flag1 = false;
        bool flag2 = false;
        std::future<int> flag_future = pool.submit(
            [](bool* flag1_, bool* flag2_) {
                *flag1_ = *flag2_ = true;
                return 42;
            },
            &flag1, &flag2);
        CHECK((flag_future.get() == 42 && flag1 && flag2));
    }
    {
        std::future<std::pair<bool, bool>> fut = pool.submit(
            [detect = DetectCopyMove()] { return std::pair(detect.copied, detect.moved); });
        std::pair<bool, bool> result = fut.get();
        CHECK((!result.first && result.second));
    }
    {
        int64_t pass_me_by_value = 0;
        pool.submit(
                [](int64_t passed_by_value) {
                    if (++passed_by_value)
                        std::this_thread::yield();
                },
                pass_me_by_value)
            .wait();
        CHECK(pass_me_by_value == 0);

        int64_t pass_me_by_ref = 0;
        pool.submit([](int64_t& passed_by_ref) { ++passed_by_ref; }, std::ref(pass_me_by_ref))
            .wait();
        CHECK(pass_me_by_ref == 1);

        int64_t pass_me_by_cref = 0;
        std::atomic<bool> release = false;
        std::future<void> fut = pool.submit(
            [&release](const int64_t& passed_by_cref) {
                while (!release)
                    std::this_thread::yield();
                CHECK(passed_by_cref == 1);
            },
            std::cref(pass_me_by_cref));

        std::this_thread::sleep_for(std::chrono::milliseconds(10));
        ++pass_me_by_cref;
        release = true;
        fut.wait();
    }
}

TEST_CASE("ThreadPool -- waitForAll") {
    ThreadPool pool;
    size_t n = pool.getThreadCount() * 2;
    auto flags = std::make_unique<std::atomic<bool>[]>(n);

    for (size_t i = 0; i < n; ++i)
        pool.pushTask([&flags, i] {
            std::this_thread::sleep_for(std::chrono::microseconds(500));
            flags[i] = true;
        });

    pool.waitForAll();
    bool allFlags = true;
    for (size_t i = 0; i < n; ++i)
        allFlags = allFlags && flags[i];
    CHECK(allFlags);
}

TEST_CASE("ThreadPool -- waitForAll blocks calling threads") {
    ThreadPool pool;
    pool.waitForAll();

    std::atomic<bool> release = false;
    pool.pushTask([&release] {
        while (!release)
            std::this_thread::yield();
    });

    constexpr size_t numTasks = 4;
    ThreadPool tempPool(numTasks);
    auto flags = std::make_unique<std::atomic<bool>[]>(numTasks);
    auto waitingTask = [&flags, &pool](size_t i) {
        pool.waitForAll();
        flags[i] = true;
    };

    for (size_t i = 0; i < numTasks; ++i)
        tempPool.pushTask(waitingTask, i);

    std::this_thread::sleep_for(std::chrono::milliseconds(10));
    bool anySet = false;
    for (size_t i = 0; i < numTasks; ++i)
        anySet = anySet || flags[i];
    CHECK(!anySet);

    release = true;
    tempPool.waitForAll();
    bool allSet = true;
    for (size_t i = 0; i < numTasks; ++i)
        allSet = allSet && flags[i];
    CHECK(allSet);
}

#if __cpp_exceptions
TEST_CASE("ThreadPool -- exception handling") {
    ThreadPool pool;
    std::future<void> fut = pool.submit([] { throw std::runtime_error("Exception thrown!"); });

    CHECK_THROWS_WITH(fut.get(), "Exception thrown!");
}
#endif

TEST_CASE("ThreadPool -- pushLoop") {
    ThreadPool pool(3);

    // Pushing an empty loop does nothing.
    bool flag = false;
    pool.pushLoop(3, 3, [&](int start, int end) { flag = true; });
    pool.waitForAll();
    CHECK(!flag);

    std::array<std::atomic<bool>, 2> flags2{false, false};
    pool.pushLoop(3, 5, [&](int start, int end) {
        for (int i = start; i < end; i++)
            flags2[i - 3] = true;
    });
    pool.waitForAll();
    CHECK(std::ranges::all_of(flags2, [](auto&& f) -> bool { return f; }));

    std::array<std::atomic<bool>, 10> flags10;
    std::ranges::fill(flags10, false);

    pool.pushLoop(3, 13, [&](int start, int end) {
        for (int i = start; i < end; i++)
            flags10[i - 3] = true;
    });
    pool.waitForAll();
    CHECK(std::ranges::all_of(flags10, [](auto&& f) -> bool { return f; }));
}

#ifdef CI_BUILD

TEST_CASE("ThreadPool -- no destruction deadlocks") {
    constexpr uint32_t tries = 1000;

    ThreadPool pool;
    uint32_t i = 0;
    pool.pushTask([&i] {
        do {
            ThreadPool tempPool;
        } while (++i < tries);
    });

    bool passed = false;
    while (true) {
        uint32_t oldIndex = i;
        pool.waitForAll(std::chrono::milliseconds(500));
        if (i == tries) {
            passed = true;
            break;
        }

        if (i <= oldIndex) {
            passed = false;
            break;
        }
    }
    CHECK(passed);
}

TEST_CASE("ThreadPool -- waitForAll no deadlock") {
    ThreadPool pool;
    ThreadPool tempPool(1);
    tempPool.pushTask([] { std::this_thread::sleep_for(std::chrono::milliseconds(500)); });

    constexpr uint32_t numTasks = 1000;
    std::atomic<uint32_t> count = 0;
    for (uint32_t j = 0; j < numTasks; ++j) {
        pool.pushTask([&tempPool, &count] {
            tempPool.waitForAll();
            ++count;
        });
    }

    bool passed = false;
    while (true) {
        uint32_t oldCount = count;
        pool.waitForAll(std::chrono::milliseconds(1000));
        if (count == numTasks) {
            passed = true;
            break;
        }

        if (count <= oldCount) {
            // Deadlock detected.
            passed = false;
            break;
        }
    }
    CHECK(passed);
}

TEST_CASE("ThreadPool -- waitForAll duration") {
    ThreadPool pool;
    std::atomic<bool> done = false;
    pool.pushTask([&done] {
        std::this_thread::sleep_for(std::chrono::milliseconds(250));
        done = true;
    });

    pool.waitForAll(std::chrono::milliseconds(10));
    CHECK(!done);

    pool.waitForAll(std::chrono::milliseconds(500));
    CHECK(done);
}

#endif
