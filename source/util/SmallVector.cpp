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

} // namespace slang::detail
