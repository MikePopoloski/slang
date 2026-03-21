//------------------------------------------------------------------------------
//! @file ThreadPool.h
//! @brief Thread pool wrapper class
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#if defined(SLANG_USE_THREADS)
#    include <BS_thread_pool.hpp>
#endif

#include "slang/util/Util.h"

namespace slang {

#if defined(SLANG_USE_THREADS)

/// @brief A thread pool for parallel execution.
///
/// This is a thin wrapper around the BS::thread_pool class that provides
/// a uniform interface regardless of whether threading is enabled at compile time.
class SLANG_EXPORT ThreadPool : public BS::thread_pool<> {
public:
    using BS::thread_pool<>::thread_pool;
};

#else

/// @brief A stub thread pool used when threading support is not compiled in.
///
/// None of the methods should be called; they will throw if invoked.
class SLANG_EXPORT ThreadPool {
public:
    explicit ThreadPool(uint32_t = 0) {}

    template<typename Index, typename F>
    void detach_loop(Index, Index, F&&) {
        die();
    }

    template<typename F>
    void detach_task(F&&) {
        die();
    }

    void wait() { die(); }

    [[nodiscard]] size_t get_thread_count() const noexcept { return 0; }

private:
    void die() const { SLANG_THROW(std::runtime_error("Thread pool is not available")); }
};

#endif

} // namespace slang
