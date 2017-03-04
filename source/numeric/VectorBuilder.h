//------------------------------------------------------------------------------
// VectorBuilder.h
// Helper type to construct SVInt instances.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "lexing/Token.h"
#include "text/SourceLocation.h"
#include "util/SmallVector.h"

#include "SVInt.h"

namespace slang {

class BumpAllocator;
class Diagnostics;

/// This class is a helper used by the parser to piece together
/// arbitrary precision integer literals.
class VectorBuilder {
public:
    VectorBuilder(Diagnostics& diagnostics);

    /// Start a new integer literal.
    void start(LiteralBase base, uint16_t size, bool isSigned, SourceLocation location);

    /// Add another token to the literal.
    void append(Token token);

    /// Finish off the literal and convert it into an SVInt instance.
    SVInt finish();

private:
    void addDigit(logic_t digit, int maxValue);

    Diagnostics& diagnostics;
    SmallVectorSized<logic_t, 16> digits;
    SourceLocation firstLocation;
    uint16_t sizeBits;
    LiteralBase literalBase;
    bool signFlag;
    bool hasUnknown;
    bool valid;
    bool first;
};

}