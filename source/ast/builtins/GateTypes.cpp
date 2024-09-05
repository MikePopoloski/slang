//------------------------------------------------------------------------------
// GateTypes.cpp
// Definitions for the built-in gate types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/MemberSymbols.h"

namespace slang::ast::builtins {

#define NL SourceLocation::NoLocation

static void gate(Compilation& c, std::string_view name,
                 std::initializer_list<PrimitivePortDirection> portDirs,
                 PrimitiveSymbol::PrimitiveKind primitiveKind = PrimitiveSymbol::Fixed) {
    auto& prim = *c.emplace<PrimitiveSymbol>(c, name, NL, primitiveKind);
    c.addGateType(prim);

    SmallVector<const PrimitivePortSymbol*> ports;
    for (auto dir : portDirs) {
        auto port = c.emplace<PrimitivePortSymbol>(c, "", NL, dir);
        prim.addMember(*port);
        ports.push_back(port);
    }

    prim.ports = ports.copy(c);
}

#define in PrimitivePortDirection::In
#define out PrimitivePortDirection::Out
#define inout PrimitivePortDirection::InOut

void registerGateTypes(Compilation& c) {
    gate(c, "cmos", {out, in, in, in});
    gate(c, "rcmos", {out, in, in, in});
    gate(c, "bufif0", {out, in, in});
    gate(c, "bufif1", {out, in, in});
    gate(c, "notif0", {out, in, in});
    gate(c, "notif1", {out, in, in});
    gate(c, "nmos", {out, in, in});
    gate(c, "pmos", {out, in, in});
    gate(c, "rnmos", {out, in, in});
    gate(c, "rpmos", {out, in, in});
    gate(c, "tranif0", {inout, inout, in}, PrimitiveSymbol::BiDiSwitch);
    gate(c, "tranif1", {inout, inout, in}, PrimitiveSymbol::BiDiSwitch);
    gate(c, "rtranif0", {inout, inout, in});
    gate(c, "rtranif1", {inout, inout, in});
    gate(c, "tran", {inout, inout}, PrimitiveSymbol::BiDiSwitch);
    gate(c, "rtran", {inout, inout});
    gate(c, "pullup", {out});
    gate(c, "pulldown", {out});

    // These are special in that they support an arbitrary number of
    // either inputs or outputs.
    gate(c, "and", {out, in}, PrimitiveSymbol::NInput);
    gate(c, "or", {out, in}, PrimitiveSymbol::NInput);
    gate(c, "nand", {out, in}, PrimitiveSymbol::NInput);
    gate(c, "nor", {out, in}, PrimitiveSymbol::NInput);
    gate(c, "xor", {out, in}, PrimitiveSymbol::NInput);
    gate(c, "xnor", {out, in}, PrimitiveSymbol::NInput);
    gate(c, "buf", {out, in}, PrimitiveSymbol::NOutput);
    gate(c, "not", {out, in}, PrimitiveSymbol::NOutput);
}

} // namespace slang::ast::builtins
