#pragma once

#include "Buffer.h"
#include "SourceLocation.h"
#include "SVInt.h"
#include "Token.h"

namespace slang {

class BumpAllocator;
class Diagnostics;

// note that this class mostly expects that you've checked errors
// elsewhere and that input is sanitized
class VectorBuilder {
public:
    VectorBuilder(BumpAllocator& alloc, Diagnostics& diagnostics);

    void start(LiteralBase base, uint16_t size, bool isSigned, SourceLocation location);
	void append(Token token);
    SVInt finish();

private:
    void addDigit(logic_t digit, int maxValue);

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    Buffer<logic_t> digits;
    SourceLocation firstLocation;
    uint16_t sizeBits;
    LiteralBase literalBase;
    bool signFlag;
    bool hasUnknown;
    bool valid;
    bool first;
};

}