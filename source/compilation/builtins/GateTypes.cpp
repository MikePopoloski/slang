//------------------------------------------------------------------------------
// GateTypes.cpp
// Definitions for the built-in gate types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Compilation.h"
#include "slang/symbols/MemberSymbols.h"

namespace slang::Builtins {

#define NL SourceLocation::NoLocation

static void gate(Compilation& c, string_view name,
                 std::initializer_list<PrimitivePortDirection> portDirs) {
    auto& prim = *c.emplace<PrimitiveSymbol>(c, name, NL);
    c.addPrimitive(prim);

    SmallVectorSized<const PrimitivePortSymbol*, 4> ports;
    for (auto dir : portDirs) {
        auto port = c.emplace<PrimitivePortSymbol>(c, "", NL, dir);
        prim.addMember(*port);
        ports.append(port);
    }

    prim.ports = ports.copy(c);
}

#define in PrimitivePortDirection::In
#define out PrimitivePortDirection::Out

void registerGateTypes(Compilation& c) {
    // TODO: some of these should be inout instead of out
    gate(c, "cmos", { out, in, in, in });
    gate(c, "rcmos", { out, in, in, in });
    gate(c, "bufif0", { out, in, in });
    gate(c, "bufif1", { out, in, in });
    gate(c, "notif0", { out, in, in });
    gate(c, "notif1", { out, in, in });
    gate(c, "nmos", { out, in, in });
    gate(c, "pmos", { out, in, in });
    gate(c, "rnmos", { out, in, in });
    gate(c, "rpmos", { out, in, in });
    gate(c, "tranif0", { out, out, in });
    gate(c, "tranif1", { out, out, in });
    gate(c, "rtranif0", { out, out, in });
    gate(c, "rtranif1", { out, out, in });
    gate(c, "tran", { out, out });
    gate(c, "rtran", { out, out });
    gate(c, "pullup", { out });
    gate(c, "pulldown", { out });

    // TODO:
    // These are special in that they support an arbitrary number of
    // either inputs or outputs.
    gate(c, "and", { out });
    gate(c, "or", { out });
    gate(c, "nand", { out });
    gate(c, "nor", { out });
    gate(c, "xor", { out });
    gate(c, "xnor", { out });
    gate(c, "buf", { out });
    gate(c, "not", { out });
}

} // namespace slang::Builtins
