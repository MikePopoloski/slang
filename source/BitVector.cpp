#include "BitVector.h"

#include "Diagnostics.h"

namespace slang {

VectorBuilder::VectorBuilder(Diagnostics& diagnostics) :
    diagnostics(diagnostics)
{
}

void VectorBuilder::start(uint32_t size) {
}

void VectorBuilder::startUnsized() {
}

void VectorBuilder::addBinaryDigit(logic_t digit) {
}

void VectorBuilder::addOctalDigit(logic_t digit) {
}

void VectorBuilder::addDecimalDigit(logic_t digit) {
}

void VectorBuilder::addHexDigit(logic_t digit) {
}

}