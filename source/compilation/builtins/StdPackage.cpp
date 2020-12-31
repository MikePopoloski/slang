//------------------------------------------------------------------------------
// StdPackage.cpp
// Definitions for the built-in 'std' package
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Compilation.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/SymbolBuilders.h"
#include "slang/types/AllTypes.h"

namespace slang::Builtins {

#define NL SourceLocation::NoLocation

static const Symbol& createProcessClass(Compilation& c) {
    ClassBuilder builder(c, "process");
    builder.type.isAbstract = true;

    auto stateEnum =
        c.emplace<EnumType>(c, NL, c.getIntType(), LookupLocation(&builder.type, 1), builder.type);
    stateEnum->systemId = INT32_MAX - 2048;

    uint64_t index = 0;
    for (auto name : { "FINISHED", "RUNNING", "WAITING", "SUSPENDED", "KILLED" }) {
        auto ev = c.emplace<EnumValueSymbol>(name, NL);
        stateEnum->addMember(*ev);
        ev->setValue(SVInt(32, index++, true));

        // Manually add these to the containing scope as well.
        builder.type.addMember(*c.emplace<TransparentMemberSymbol>(*ev));
    }

    auto stateTypedef = c.emplace<TypeAliasType>("state", NL);
    stateTypedef->targetType.setType(*stateEnum);
    builder.type.addMember(*stateTypedef);

    auto& void_t = c.getVoidType();
    auto self = builder.addMethod("self", builder.type);
    self.addFlags(MethodFlags::Static);

    builder.addMethod("status", *stateTypedef);
    builder.addMethod("kill", void_t);
    builder.addMethod("await", void_t, SubroutineKind::Task);
    builder.addMethod("suspend", void_t);
    builder.addMethod("resume", void_t);
    builder.addMethod("get_randstate", c.getStringType());

    auto srandom = builder.addMethod("srandom", void_t);
    srandom.addArg("seed", c.getIntType());

    auto set_randstate = builder.addMethod("set_randstate", void_t);
    set_randstate.addArg("state", c.getStringType());

    return builder.type;
}

static const Symbol& createSemaphoreClass(Compilation& c) {
    ClassBuilder builder(c, "semaphore");

    auto& void_t = c.getVoidType();
    auto& int_t = c.getIntType();
    auto defaultZero = SVInt(32, 0u, true);
    auto defaultOne = SVInt(32, 1u, true);

    auto ctor = builder.addMethod("new", void_t);
    ctor.addFlags(MethodFlags::Constructor);
    ctor.addArg("keyCount", int_t, ArgumentDirection::In, defaultZero);

    auto put = builder.addMethod("put", void_t);
    put.addArg("keyCount", int_t, ArgumentDirection::In, defaultOne);

    auto get = builder.addMethod("get", void_t, SubroutineKind::Task);
    get.addArg("keyCount", int_t, ArgumentDirection::In, defaultOne);

    auto try_get = builder.addMethod("try_get", int_t);
    try_get.addArg("keyCount", int_t, ArgumentDirection::In, defaultOne);

    return builder.type;
}

static const Symbol& createRandomizeFunc(Compilation& c) {
    MethodBuilder builder(c, "randomize", c.getIntType());
    builder.addFlags(MethodFlags::Randomize);
    return builder.symbol;
}

const PackageSymbol& createStdPackage(Compilation& c) {
    auto pkg = c.emplace<PackageSymbol>(c, "std", NL, c.getWireNetType());
    pkg->addMember(createProcessClass(c));
    pkg->addMember(createSemaphoreClass(c));
    pkg->addMember(createRandomizeFunc(c));

    return *pkg;
}

} // namespace slang::Builtins
