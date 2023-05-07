//------------------------------------------------------------------------------
// SmallVector.cpp
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/SmallVector.h"

namespace slang::detail {

void throwOutOfRange() {
    SLANG_THROW(std::out_of_range("vector index out of range"));
}

void throwLengthError() {
    SLANG_THROW(std::length_error("vector is at maximum size"));
}

void* allocArray(size_t capacity, size_t typeSize) {
    void* result = std::malloc(capacity * typeSize);
    if (!result)
        SLANG_THROW(std::bad_alloc());

    return result;
}

} // namespace slang::detail
