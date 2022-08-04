//------------------------------------------------------------------------------
// MIRBuilder.cpp
// MIR construction
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/mir/MIRBuilder.h"

#include "slang/compilation/Compilation.h"
#include "slang/mir/Procedure.h"
#include "slang/symbols/ASTVisitor.h"

namespace slang::mir {

MIRBuilder::MIRBuilder(Compilation& compilation) : compilation(compilation) {
}

MIRBuilder::~MIRBuilder() = default;

void MIRBuilder::elaborate() {
    // TODO: support more than just initial blocks
    compilation.getRoot().visit(makeVisitor([&](const ProceduralBlockSymbol& block) {
        if (block.procedureKind != ProceduralBlockKind::Initial)
            return;

        initialProcs.emplace_back(std::make_unique<Procedure>(*this, block));
    }));
}

MIRValue MIRBuilder::emitConst(const Type& type, const ConstantValue& val) {
    return MIRValue(*constantAlloc.emplace(type, val));
}

MIRValue MIRBuilder::emitConst(const Type& type, ConstantValue&& val) {
    return MIRValue(*constantAlloc.emplace(type, std::move(val)));
}

MIRValue MIRBuilder::emitGlobal(const VariableSymbol& symbol) {
    auto& val = globalMap[&symbol];
    if (val)
        return val;

    ASSERT(symbol.lifetime == VariableLifetime::Static);
    val = MIRValue::global(globals.size());
    globals.push_back(&symbol);
    return val;
}

const VariableSymbol& MIRBuilder::getGlobal(MIRValue val) const {
    ASSERT(val.getKind() == MIRValue::Global);
    return *globals[val.asIndex()];
}

} // namespace slang::mir
