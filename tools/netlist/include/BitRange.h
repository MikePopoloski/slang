//------------------------------------------------------------------------------
//! @file BitRange.h
//! @brieif A class to represent a bit range.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <ostream>
#include "fmt/format.h"

#include "slang/numeric/SVInt.h"


struct BitRange {
  slang::bitwidth_t start;
  slang::bitwidth_t end;
  BitRange(size_t index) : start(index), end(index) {}
  BitRange(size_t start, size_t end) : start(start), end(end) {
    SLANG_ASSERT(start <= end);
  }
  /// Given another range, return true if it overlaps with this range.
  inline bool overlap(BitRange other) const {
      return start <= other.end && other.start <= end;
  }
  /// Given another range, return true if it is contained within this range.
  inline bool contains(BitRange other) const {
      return other.start >= start && other.end <= end;
  }
  /// Equality.
  friend bool operator==(BitRange const & A, BitRange const & B) noexcept {
      return A.start == B.start && A.end == B.end;
  }
  // Output to stream.
  friend std::ostream& operator<<(std::ostream& os, const BitRange& range) {
      os << fmt::format("BitRange {}", range.toString());
      return os;
  }
  size_t size() const { return end - start; }
  std::string toString() const { return fmt::format("[{}:{}]", end, start); }
};


