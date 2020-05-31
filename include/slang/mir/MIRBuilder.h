//------------------------------------------------------------------------------
//! @file MIRBuilder.h
//! @brief MIR construction
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>
#include <vector>

#include "slang/mir/Instr.h"
#include "slang/util/BumpAllocator.h"

namespace slang {

class Compilation;
class ConstantValue;
class Type;
class VariableSymbol;

namespace mir {

class MIRBuilder : public BumpAllocator {
public:
    Compilation& compilation;

    MIRBuilder(Compilation& compilation) : compilation(compilation) {}

    MIRValue emitConst(const Type& type, const ConstantValue& val);
    MIRValue emitConst(const Type& type, ConstantValue&& val);
    MIRValue emitGlobal(const VariableSymbol& symbol);

    const VariableSymbol& getGlobal(MIRValue val) const;
    span<const VariableSymbol* const> getGlobals() const { return globals; }

private:
    TypedBumpAllocator<TypedConstantValue> constantAlloc;
    std::vector<const VariableSymbol*> globals;
    flat_hash_map<const VariableSymbol*, MIRValue> globalMap;
};

} // namespace mir

} // namespace slang