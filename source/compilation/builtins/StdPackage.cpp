//------------------------------------------------------------------------------
// StdPackage.cpp
// Definitions for the built-in 'std' package
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/LiteralExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/types/AllTypes.h"

namespace slang::Builtins {

#define NL SourceLocation::NoLocation

class SubroutineBuilder {
public:
    Compilation& compilation;
    SubroutineSymbol* func;
    SmallVectorSized<const FormalArgumentSymbol*, 4> args;

    SubroutineBuilder(Compilation& compilation, string_view name, const Type& retType,
                      SubroutineKind kind = SubroutineKind::Function) :
        compilation(compilation) {

        func = compilation.emplace<SubroutineSymbol>(compilation, name, NL,
                                                     VariableLifetime::Automatic, kind);
        func->declaredReturnType.setType(retType);
        func->flags = MethodFlags::NotConst;
    }

    FormalArgumentSymbol& addArg(string_view name, const Type& type,
                                 ArgumentDirection direction = ArgumentDirection::In) {
        auto arg = compilation.emplace<FormalArgumentSymbol>(name, NL, direction,
                                                             VariableLifetime::Automatic);
        arg->setType(type);
        func->addMember(*arg);
        args.append(arg);
        return *arg;
    }

    void finishArgs() { func->setArguments(args.copy(compilation)); }
};

class ClassBuilder {
public:
    Compilation& compilation;
    ClassType* type;

    ClassBuilder(Compilation& compilation, string_view name) : compilation(compilation) {
        type = compilation.emplace<ClassType>(compilation, name, NL);
    }

    SubroutineBuilder method(string_view name, const Type& retType,
                             SubroutineKind kind = SubroutineKind::Function) {
        SubroutineBuilder sub(compilation, name, retType, kind);
        type->addMember(*sub.func);
        return sub;
    }
};

static const Symbol& createProcessClass(Compilation& c) {
    ClassBuilder builder(c, "process");
    builder.type->isAbstract = true;

    auto stateEnum =
        c.emplace<EnumType>(c, NL, c.getIntType(), LookupLocation(builder.type, 1), *builder.type);
    stateEnum->systemId = INT32_MAX - 2048;

    uint64_t index = 0;
    for (auto name : { "FINISHED", "RUNNING", "WAITING", "SUSPENDED", "KILLED" }) {
        auto ev = c.emplace<EnumValueSymbol>(name, NL);
        stateEnum->addMember(*ev);
        ev->setValue(SVInt(32, index++, true));

        // Manually add these to the containing scope as well.
        builder.type->addMember(*c.emplace<TransparentMemberSymbol>(*ev));
    }

    auto stateTypedef = c.emplace<TypeAliasType>("state", NL);
    stateTypedef->targetType.setType(*stateEnum);
    builder.type->addMember(*stateTypedef);

    auto& void_t = c.getVoidType();
    auto self = builder.method("self", *builder.type);
    self.func->flags |= MethodFlags::Static;

    builder.method("status", *stateTypedef);
    builder.method("kill", void_t);
    builder.method("await", void_t, SubroutineKind::Task);
    builder.method("suspend", void_t);
    builder.method("resume", void_t);
    builder.method("get_randstate", c.getStringType());

    auto srandom = builder.method("srandom", void_t);
    srandom.addArg("seed", c.getIntType());
    srandom.finishArgs();

    auto set_randstate = builder.method("set_randstate", void_t);
    set_randstate.addArg("state", c.getStringType());
    set_randstate.finishArgs();

    return *builder.type;
}

static const Symbol& createSemaphoreClass(Compilation& c) {
    ClassBuilder builder(c, "semaphore");

    auto& void_t = c.getVoidType();
    auto& int_t = c.getIntType();

    auto& defaultZero = IntegerLiteral::fromConstant(c, SVInt(32, 0u, true));
    auto& defaultOne = IntegerLiteral::fromConstant(c, SVInt(32, 1u, true));

    auto ctor = builder.method("new", void_t);
    ctor.func->flags |= MethodFlags::Constructor;
    ctor.addArg("keyCount", int_t).setInitializer(defaultZero);
    ctor.finishArgs();

    auto put = builder.method("put", void_t);
    put.addArg("keyCount", int_t).setInitializer(defaultOne);
    put.finishArgs();

    auto get = builder.method("get", void_t, SubroutineKind::Task);
    get.addArg("keyCount", int_t).setInitializer(defaultOne);
    get.finishArgs();

    auto try_get = builder.method("try_get", int_t);
    try_get.addArg("keyCount", int_t).setInitializer(defaultOne);
    try_get.finishArgs();

    return *builder.type;
}

const PackageSymbol& createStdPackage(Compilation& c) {
    auto pkg = c.emplace<PackageSymbol>(c, "std", NL, c.getWireNetType());
    pkg->addMember(createProcessClass(c));
    pkg->addMember(createSemaphoreClass(c));
    return *pkg;
}

} // namespace slang::Builtins
