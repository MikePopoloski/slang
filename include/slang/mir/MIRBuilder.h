//------------------------------------------------------------------------------
//! @file MIRBuilder.h
//! @brief MIR construction
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

namespace slang::mir {

class MIRBuilder {
public:
    Compilation& compilation;

    MIRBuilder(Compilation& compilation) : compilation(compilation) {}
};

} // namespace slang::mir