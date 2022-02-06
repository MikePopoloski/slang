//------------------------------------------------------------------------------
// SymbolBuilders.cpp
// Contains helpers for constructing symbols programmatically
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/SymbolBuilders.h"

#include "slang/binding/LiteralExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/types/AllTypes.h"
#include "slang/types/Type.h"

namespace slang {

#define NL SourceLocation::NoLocation

MethodBuilder::MethodBuilder(Compilation& compilation, string_view name, const Type& returnType,
                             SubroutineKind kind) :
    compilation(compilation),
    symbol(*compilation.emplace<SubroutineSymbol>(compilation, name, NL,
                                                  VariableLifetime::Automatic, kind)) {
    symbol.declaredReturnType.setType(returnType);
    symbol.flags = MethodFlags::NotConst;
}

MethodBuilder::MethodBuilder(MethodBuilder&& other) noexcept :
    compilation(other.compilation), symbol(other.symbol) {
    // Clear arguments in the other builder so that its destructor doesn't overwrite
    // any arguments we may add from here on out.
    args.appendRange(other.args);
    other.args.clear();
}

MethodBuilder::~MethodBuilder() {
    if (!args.empty())
        symbol.setArguments(args.copy(compilation));
}

FormalArgumentSymbol& MethodBuilder::addArg(string_view name, const Type& type,
                                            ArgumentDirection direction,
                                            optional<SVInt> defaultValue) {
    auto arg =
        compilation.emplace<FormalArgumentSymbol>(name, NL, direction, VariableLifetime::Automatic);
    arg->setType(type);
    symbol.addMember(*arg);
    args.append(arg);

    if (defaultValue) {
        ASSERT(type.isIntegral());
        arg->setInitializer(IntegerLiteral::fromConstant(compilation, *defaultValue));
    }

    return *arg;
}

FormalArgumentSymbol& MethodBuilder::copyArg(const FormalArgumentSymbol& fromArg) {
    auto arg = compilation.emplace<FormalArgumentSymbol>(fromArg.name, fromArg.location,
                                                         fromArg.direction, fromArg.lifetime);
    arg->flags = fromArg.flags;
    symbol.addMember(*arg);
    args.append(arg);

    auto& argDT = *arg->getDeclaredType();
    auto& fromDT = *fromArg.getDeclaredType();
    argDT.setLink(fromDT);

    if (auto expr = fromDT.getInitializerSyntax())
        argDT.setInitializerSyntax(*expr, fromDT.getInitializerLocation());

    return *arg;
}

void MethodBuilder::addFlags(bitmask<MethodFlags> flags) {
    symbol.flags |= flags;
}

ClassBuilder::ClassBuilder(Compilation& compilation, string_view name) :
    compilation(compilation), type(*compilation.emplace<ClassType>(compilation, name, NL)) {
}

ClassBuilder::ClassBuilder(Compilation& compilation, ClassType& existing) :
    compilation(compilation), type(existing) {
}

MethodBuilder ClassBuilder::addMethod(string_view name, const Type& retType, SubroutineKind kind) {
    MethodBuilder method(compilation, name, retType, kind);
    type.addMember(method.symbol);
    return method;
}

StructBuilder::StructBuilder(const Scope& scope, LookupLocation lookupLocation) :
    compilation(scope.getCompilation()), type(*compilation.emplace<UnpackedStructType>(
                                             compilation, NL, BindContext(scope, lookupLocation))) {
}

void StructBuilder::addField(string_view name, const Type& fieldType,
                             bitmask<VariableFlags> flags) {
    auto field = compilation.emplace<FieldSymbol>(name, NL, currFieldIndex);
    field->flags = flags;
    field->setType(fieldType);
    type.addMember(*field);
    currFieldIndex++;
}

void StructBuilder::addField(string_view name, const DeclaredType& typeLink,
                             bitmask<VariableFlags> flags) {
    auto field = compilation.emplace<FieldSymbol>(name, NL, currFieldIndex);
    field->flags = flags;
    field->getDeclaredType()->setLink(typeLink);
    type.addMember(*field);
    currFieldIndex++;
}

} // namespace slang
