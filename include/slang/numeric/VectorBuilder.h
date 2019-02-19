//------------------------------------------------------------------------------
// VectorBuilder.h
// Helper type to construct SVInt instances.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/SVInt.h"
#include "slang/parsing/Token.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/SmallVector.h"

namespace slang {

class BumpAllocator;
class Diagnostics;

/// This class is a helper used by the parser to piece together
/// arbitrary precision integer literals.
class VectorBuilder {
public:
    VectorBuilder(Diagnostics& diagnostics);

    /// Start a new integer literal.
    void start(LiteralBase base, bitwidth_t size, bool isSigned, SourceLocation location);

    /// Add another token to the literal.
    int append(Token token);

    /// Finish off the literal and convert it into an SVInt instance.
    SVInt finish();

private:
    void addDigit(logic_t digit, int maxValue);

    Diagnostics& diagnostics;
    SmallVectorSized<logic_t, 16> digits;
    SourceLocation firstLocation;
    bitwidth_t sizeBits = 0;
    LiteralBase literalBase = LiteralBase::Binary;
    SVInt decimalValue;
    bool signFlag = false;
    bool hasUnknown = false;
    bool valid = false;
    bool first = false;
};

} // namespace slang