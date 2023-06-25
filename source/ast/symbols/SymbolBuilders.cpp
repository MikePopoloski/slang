//------------------------------------------------------------------------------
// SymbolBuilders.cpp
// Contains helpers for constructing symbols programmatically
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/SymbolBuilders.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/Type.h"

namespace slang::ast {

#define NL SourceLocation::NoLocation

MethodBuilder::MethodBuilder(Compilation& compilation, std::string_view name,
                             const Type& returnType, SubroutineKind kind) :
    compilation(compilation),
    symbol(*compilation.emplace<SubroutineSymbol>(compilation, name, NL,
                                                  VariableLifetime::Automatic, kind)) {
    symbol.declaredReturnType.setType(returnType);
    symbol.flags = MethodFlags::BuiltIn;
}

MethodBuilder::MethodBuilder(MethodBuilder&& other) noexcept :
    compilation(other.compilation), symbol(other.symbol) {
    // Clear arguments in the other builder so that its destructor doesn't overwrite
    // any arguments we may add from here on out.
    args.append_range(other.args);
    other.args.clear();
}

MethodBuilder::~MethodBuilder() {
    if (!args.empty())
        symbol.setArguments(args.copy(compilation));
}

FormalArgumentSymbol& MethodBuilder::addArg(std::string_view name, const Type& type,
                                            ArgumentDirection direction,
                                            std::optional<SVInt> defaultValue) {
    auto arg = compilation.emplace<FormalArgumentSymbol>(name, NL, direction,
                                                         VariableLifetime::Automatic);
    arg->setType(type);
    symbol.addMember(*arg);
    args.push_back(arg);

    if (defaultValue) {
        SLANG_ASSERT(type.isIntegral());
        arg->setDefaultValue(&IntegerLiteral::fromConstant(compilation, *defaultValue));
    }

    return *arg;
}

FormalArgumentSymbol& MethodBuilder::copyArg(const FormalArgumentSymbol& fromArg) {
    auto arg = compilation.emplace<FormalArgumentSymbol>(fromArg.name, fromArg.location,
                                                         fromArg.direction, fromArg.lifetime);
    arg->flags = fromArg.flags;
    arg->setDefaultValue(fromArg.getDefaultValue());
    symbol.addMember(*arg);
    args.push_back(arg);

    auto& argDT = *arg->getDeclaredType();
    auto& fromDT = *fromArg.getDeclaredType();
    argDT.setLink(fromDT);

    return *arg;
}

void MethodBuilder::addFlags(bitmask<MethodFlags> flags) {
    symbol.flags |= flags;
}

ClassBuilder::ClassBuilder(Compilation& compilation, std::string_view name) :
    compilation(compilation), type(*compilation.emplace<ClassType>(compilation, name, NL)) {
}

ClassBuilder::ClassBuilder(Compilation& compilation, ClassType& existing) :
    compilation(compilation), type(existing) {
}

MethodBuilder ClassBuilder::addMethod(std::string_view name, const Type& retType,
                                      SubroutineKind kind) {
    MethodBuilder method(compilation, name, retType, kind);
    type.addMember(method.symbol);
    return method;
}

StructBuilder::StructBuilder(const Scope& scope, LookupLocation lookupLocation) :
    compilation(scope.getCompilation()),
    type(*compilation.emplace<UnpackedStructType>(compilation, NL,
                                                  ASTContext(scope, lookupLocation))) {
}

void StructBuilder::addField(std::string_view name, const Type& fieldType,
                             bitmask<VariableFlags> flags) {
    auto field = compilation.emplace<FieldSymbol>(name, NL, currBitOffset, currFieldIndex);
    field->flags = flags;
    field->setType(fieldType);
    type.addMember(*field);

    currFieldIndex++;
    currBitOffset += fieldType.getSelectableWidth();
    type.selectableWidth = currBitOffset;
}

} // namespace slang::ast
