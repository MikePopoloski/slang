//------------------------------------------------------------------------------
//! @file ScopeGuard.h
//! @brief Contains the ScopeGuard utility class
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <utility>

namespace slang {

/// A simple guard class that ensures a given function is invoked when the
/// guard object is destroyed.
template<typename F>
class ScopeGuard {
public:
    explicit ScopeGuard(F&& f) noexcept : func(std::move(f)) {}

    ScopeGuard(ScopeGuard&& other) noexcept :
        func(std::move(other.func)), valid(std::exchange(other.valid, false)) {}

    ScopeGuard(const ScopeGuard&) = delete;
    ScopeGuard& operator=(const ScopeGuard&) = delete;
    ScopeGuard& operator=(ScopeGuard&&) = delete;

    ~ScopeGuard() noexcept {
        if (valid)
            func();
    }

    void release() noexcept { valid = false; }

private:
    F func;
    bool valid = true;
};

template<typename F>
explicit ScopeGuard(F&& f) -> ScopeGuard<F>;

} // namespace slang
