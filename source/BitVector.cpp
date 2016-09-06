#include "BitVector.h"

#include "Diagnostics.h"

namespace slang {

const logic_t logic_t::x = 1 << 7;
const logic_t logic_t::z = 1 << 6;

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