//------------------------------------------------------------------------------
// ThreadPool.cpp
// Thread pool wrapper class
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/ThreadPool.h"

#if defined(SLANG_USE_THREADS)

namespace BS {

thread_local std::optional<std::size_t> this_thread::my_index = std::nullopt;
thread_local std::optional<void*> this_thread::my_pool = std::nullopt;

} // namespace BS

#endif
