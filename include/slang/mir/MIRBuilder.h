//------------------------------------------------------------------------------
//! @file MIRBuilder.h
//! @brief MIR construction
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <vector>

#include "slang/mir/Instr.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/Hash.h"

namespace slang {

class Compilation;
class ConstantValue;
class Type;
class VariableSymbol;

namespace mir {

class Procedure;

class MIRBuilder : public BumpAllocator {
public:
    Compilation& compilation;

    explicit MIRBuilder(Compilation& compilation);
    ~MIRBuilder();

    void elaborate();

    MIRValue emitConst(const Type& type, const ConstantValue& val);
    MIRValue emitConst(const Type& type, ConstantValue&& val);
    MIRValue emitGlobal(const VariableSymbol& symbol);

    span<const std::unique_ptr<Procedure>> getInitialProcs() const { return initialProcs; }

    const VariableSymbol& getGlobal(MIRValue val) const;
    span<const VariableSymbol* const> getGlobals() const { return globals; }

private:
    TypedBumpAllocator<TypedConstantValue> constantAlloc;
    std::vector<const VariableSymbol*> globals;
    std::vector<std::unique_ptr<Procedure>> initialProcs;
    flat_hash_map<const VariableSymbol*, MIRValue> globalMap;
};

} // namespace mir

} // namespace slang
