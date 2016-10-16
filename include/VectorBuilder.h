#pragma once

#include "Buffer.h"
#include "SourceLocation.h"
#include "SVInt.h"

namespace slang {

class BumpAllocator;
class Diagnostics;

// note that this class mostly expects that you've checked errors
// elsewhere and that input is sanitized
class VectorBuilder {
public:
    VectorBuilder(BumpAllocator& alloc, Diagnostics& diagnostics);

    void start(LiteralBase base, uint32_t size, SourceLocation location);
	void append(Token token);
    SVInt finish();

private:
    void commonAddDigit(logic_t digit, int maxValue);
	void checkSize(uint64_t value, uint32_t size, SourceLocation location);

    uint64_t calcBinary() const;
    uint64_t calcOctal() const;
    uint64_t calcHex() const;
    uint64_t calcDecimal(SourceLocation location) const;

	void addBinaryDigit(logic_t digit);
	void addOctalDigit(logic_t digit);
	void addDecimalDigit(logic_t digit);
	void addHexDigit(logic_t digit);

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    Buffer<logic_t> digits;
    bool hasUnknown;
};

}