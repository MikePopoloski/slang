//------------------------------------------------------------------------------
// SourceLocation.cpp
// Source element location tracking
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/text/SourceLocation.h"

namespace slang {

const SourceLocation SourceLocation::NoLocation{BufferID((1u << 28) - 1, ""), (1ull << 36) - 1};
const SourceRange SourceRange::NoLocation{SourceLocation::NoLocation, SourceLocation::NoLocation};

} // namespace slang
