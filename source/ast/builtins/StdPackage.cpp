//------------------------------------------------------------------------------
// StdPackage.cpp
// Definitions for the built-in 'std' package
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/SymbolBuilders.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::ast::builtins {

using namespace syntax;

#define NL SourceLocation::NoLocation

static const Symbol& createProcessClass(Compilation& c) {
    ClassBuilder builder(c, "process");
    builder.type.isAbstract = true;
    builder.type.isFinal = true;

    ASTContext enumCtx(builder.type, LookupLocation(&builder.type, 1));
    auto stateEnum = c.emplace<EnumType>(c, NL, c.getIntType(), enumCtx);
    stateEnum->systemId = INT32_MAX - 2048;

    uint64_t index = 0;
    for (auto name : {"FINISHED", "RUNNING", "WAITING", "SUSPENDED", "KILLED"}) {
        auto ev = c.emplace<EnumValueSymbol>(name, NL);
        ev->setType(*stateEnum);
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

static const Symbol& createMailboxClass(Compilation& c) {
    auto specialize = [](Compilation& c, ClassType& ct, SourceLocation) {
        // Get a reference to the type parameter so we can use it
        // for functions that we build.
        auto& typeParam = ct.find<TypeParameterSymbol>("T");
        auto& t = typeParam.targetType.getType();

        ClassBuilder builder(c, ct);

        auto& void_t = c.getVoidType();
        auto& int_t = c.getIntType();
        auto defaultZero = SVInt(32, 0u, true);
        auto defaultOne = SVInt(32, 1u, true);

        auto ctor = builder.addMethod("new", void_t);
        ctor.addFlags(MethodFlags::Constructor);
        ctor.addArg("bound", int_t, ArgumentDirection::In, defaultZero);

        builder.addMethod("num", int_t);

        auto put = builder.addMethod("put", void_t, SubroutineKind::Task);
        put.addArg("message", t);

        auto try_put = builder.addMethod("try_put", int_t);
        try_put.addArg("message", t);

        auto get = builder.addMethod("get", void_t, SubroutineKind::Task);
        get.addArg("message", t, ArgumentDirection::Ref);

        auto try_get = builder.addMethod("try_get", int_t);
        try_get.addArg("message", t, ArgumentDirection::Ref);

        auto peek = builder.addMethod("peek", void_t, SubroutineKind::Task);
        peek.addArg("message", t, ArgumentDirection::Ref);

        auto try_peek = builder.addMethod("try_peek", int_t);
        try_peek.addArg("message", t, ArgumentDirection::Ref);
    };

    auto& mailbox = *c.allocGenericClass("mailbox", NL, specialize);
    mailbox.addParameterDecl(
        DefinitionSymbol::ParameterDecl("T", NL, false, true, &c.getType(SyntaxKind::Untyped)));

    return mailbox;
}

static const Symbol& createRandomizeFunc(Compilation& c) {
    MethodBuilder builder(c, "randomize", c.getIntType());
    builder.addFlags(MethodFlags::Randomize);
    return builder.symbol;
}

static const Symbol& createWeakReference(Compilation& c) {
    auto specialize = [](Compilation& c, ClassType& ct, SourceLocation instanceLoc) {
        // Get a reference to the type parameter so we can use it
        // for functions that we build.
        auto& typeParam = ct.find<TypeParameterSymbol>("T");
        auto& t = typeParam.targetType.getType();

        if (!t.isClass() && !t.isError())
            ct.addDiag(diag::TypeIsNotAClass, instanceLoc) << t;

        if (auto lv = c.languageVersion(); lv < LanguageVersion::v1800_2023)
            ct.addDiag(diag::WrongLanguageVersion, instanceLoc) << toString(lv);

        ClassBuilder builder(c, ct);

        auto& void_t = c.getVoidType();

        auto ctor = builder.addMethod("new", void_t);
        ctor.addFlags(MethodFlags::Constructor);
        ctor.addArg("referent", t, ArgumentDirection::In);

        builder.addMethod("get", t);
        builder.addMethod("clear", void_t);

        auto get_id = builder.addMethod("get_id", c.getType(SyntaxKind::LongIntType));
        get_id.addArg("obj", t, ArgumentDirection::In);
        get_id.addFlags(MethodFlags::Static);
    };

    auto& weakRef = *c.allocGenericClass("weak_reference", NL, specialize);
    weakRef.addParameterDecl(DefinitionSymbol::ParameterDecl("T", NL, false, true, nullptr));

    return weakRef;
}

const PackageSymbol& createStdPackage(Compilation& c) {
    auto pkg = c.emplace<PackageSymbol>(c, "std", NL, c.getWireNetType(), VariableLifetime::Static);
    pkg->addMember(createProcessClass(c));
    pkg->addMember(createSemaphoreClass(c));
    pkg->addMember(createMailboxClass(c));
    pkg->addMember(createRandomizeFunc(c));
    pkg->addMember(createWeakReference(c));

    return *pkg;
}

} // namespace slang::ast::builtins
