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

static void gate(Compilation& c, string_view name) {
    auto& prim = *c.emplace<PrimitiveSymbol>(c, name, NL);
    c.addPrimitive(prim);
}

void registerGateTypes(Compilation& c) {
    gate(c, "cmos");
    gate(c, "rcmos");
    gate(c, "bufif0");
    gate(c, "bufif1");
    gate(c, "notif0");
    gate(c, "notif1");
    gate(c, "nmos");
    gate(c, "pmos");
    gate(c, "rnmos");
    gate(c, "rpmos");
    gate(c, "and");
    gate(c, "or");
    gate(c, "nand");
    gate(c, "nor");
    gate(c, "xor");
    gate(c, "xnor");
    gate(c, "buf");
    gate(c, "not");
    gate(c, "tranif0");
    gate(c, "tranif1");
    gate(c, "rtranif0");
    gate(c, "rtranif1");
    gate(c, "tran");
    gate(c, "rtran");
    gate(c, "pullup");
    gate(c, "pulldown");
}

} // namespace slang::Builtins
