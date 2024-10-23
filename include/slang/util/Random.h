//------------------------------------------------------------------------------
//! @file Random.h
//! @brief Utility functions related to randomization
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <algorithm>
#include <array>
#include <functional>
#include <random>

#include "slang/util/Util.h"

namespace slang {

/// Gets a (mostly) uniformly distributed value within the provided [min,max] range.
/// This is a poor man's implementation of std::uniform_int_distribution because
/// the standard type isn't required to produce identical results across implementations.
///
/// This implementation is potentially slightly biased if you use a large range but
/// slang doesn't need super precisely distributed random numbers for anything so it's fine.
template<typename TGenerator, typename TValue>
static TValue getUniformIntDist(TGenerator& gen, TValue min, TValue max) {
    TValue range = max - min + 1;
    return (gen() % range) + min;
}

/// Create a randomly seeded random number generator.
template<typename T>
static T createRandomGenerator() {
    auto constexpr seedBytes = sizeof(typename T::result_type) * T::state_size;
    auto constexpr seedLen = seedBytes / sizeof(std::seed_seq::result_type);
    auto seed = std::array<std::seed_seq::result_type, seedLen>();
    auto dev = std::random_device();
    std::ranges::generate_n(begin(seed), seedLen, std::ref(dev));
    auto seedSeq = std::seed_seq(begin(seed), end(seed));
    return T{seedSeq};
}

} // namespace slang
