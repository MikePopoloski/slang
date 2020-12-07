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
#include "slang/types/AllTypes.h"

namespace slang::Builtins {

#define NL SourceLocation::NoLocation

static const Symbol& createProcessClass(Compilation& c) {
    auto ct = c.emplace<ClassType>(c, "process", NL);
    ct->isAbstract = true;

    auto stateEnum = c.emplace<EnumType>(c, NL, c.getIntType(), LookupLocation(ct, 1), *ct);
    stateEnum->systemId = INT32_MAX - 2048;

    int index = 0;
    for (auto name : { "FINISHED", "RUNNING", "WAITING", "SUSPENDED", "KILLED" }) {
        auto ev = c.emplace<EnumValueSymbol>(name, NL);
        stateEnum->addMember(*ev);
        ev->setValue(SVInt(32, index++, true));

        // Manually add these to the containing scope as well.
        ct->addMember(*c.emplace<TransparentMemberSymbol>(*ev));
    }

    auto stateTypedef = c.emplace<TypeAliasType>("state", NL);
    stateTypedef->targetType.setType(*stateEnum);
    ct->addMember(*stateTypedef);

    auto makeFunc = [&](string_view name, const Type& retType,
                        SubroutineKind kind = SubroutineKind::Function) {
        auto func = c.emplace<SubroutineSymbol>(c, name, NL, VariableLifetime::Automatic, kind);
        func->declaredReturnType.setType(retType);
        func->flags = MethodFlags::NotConst;
        ct->addMember(*func);
        return func;
    };

    auto makeArg = [&](Scope* parent, string_view name, const Type& type) {
        auto arg = c.emplace<FormalArgumentSymbol>(name, NL, ArgumentDirection::In,
                                                   VariableLifetime::Automatic);
        arg->setType(type);
        parent->addMember(*arg);
        return arg;
    };

    auto setArgs = [&](SubroutineSymbol* sub, const FormalArgumentSymbol* arg) {
        SmallVectorSized<const FormalArgumentSymbol*, 2> args;
        args.append(arg);
        sub->setArguments(args.copy(c));
    };

    auto& void_t = c.getVoidType();
    auto self = makeFunc("self", *ct);
    self->flags |= MethodFlags::Static;

    makeFunc("status", *stateTypedef);
    makeFunc("kill", void_t);
    makeFunc("await", void_t, SubroutineKind::Task);
    makeFunc("suspend", void_t);
    makeFunc("resume", void_t);
    makeFunc("get_randstate", c.getStringType());

    auto srandom = makeFunc("srandom", void_t);
    setArgs(srandom, makeArg(srandom, "seed", c.getIntType()));

    auto set_randstate = makeFunc("set_randstate", void_t);
    setArgs(set_randstate, makeArg(set_randstate, "state", c.getStringType()));

    return *ct;
}

const PackageSymbol& createStdPackage(Compilation& c) {
    auto pkg = c.emplace<PackageSymbol>(c, "std", NL, c.getWireNetType());
    pkg->addMember(createProcessClass(c));
    return *pkg;
}

} // namespace slang::Builtins
