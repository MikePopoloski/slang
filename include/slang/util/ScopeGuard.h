//------------------------------------------------------------------------------
// ScopeGuard.h
// Contains the ScopeGuard utility class.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

namespace slang {

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

private:
    F func;
    bool valid = true;
};

} // namespace slang