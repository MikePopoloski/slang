//------------------------------------------------------------------------------
// TypeProvider.cpp
// Interface for accessing simple types during AST construction
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/TypeProvider.h"

#include "builtins/Builtins.h"

namespace slang::ast {

const Type& TypeProvider::getBitType() const {
    return builtins::Builtins::Instance.bitType;
}

const Type& TypeProvider::getLogicType() const {
    return builtins::Builtins::Instance.logicType;
}

const Type& TypeProvider::getIntType() const {
    return builtins::Builtins::Instance.intType;
}

const Type& TypeProvider::getByteType() const {
    return builtins::Builtins::Instance.byteType;
}

const Type& TypeProvider::getIntegerType() const {
    return builtins::Builtins::Instance.integerType;
}

const Type& TypeProvider::getRealType() const {
    return builtins::Builtins::Instance.realType;
}

const Type& TypeProvider::getShortRealType() const {
    return builtins::Builtins::Instance.shortRealType;
}

const Type& TypeProvider::getStringType() const {
    return builtins::Builtins::Instance.stringType;
}

const Type& TypeProvider::getVoidType() const {
    return builtins::Builtins::Instance.voidType;
}

const Type& TypeProvider::getErrorType() const {
    return ErrorType::Instance;
}

const Type& TypeProvider::getNullType() const {
    return builtins::Builtins::Instance.nullType;
}

const Type& TypeProvider::getUnboundedType() const {
    return builtins::Builtins::Instance.unboundedType;
}

const Type& TypeProvider::getTypeRefType() const {
    return builtins::Builtins::Instance.typeRefType;
}

const Type& TypeProvider::getType(bitwidth_t width, bitmask<IntegralFlags> flags) const {
    SLANG_ASSERT(width > 0 && width <= SVInt::MAX_BITS);
    return *alloc.emplace<PackedArrayType>(getScalarType(flags),
                                           ConstantRange{int32_t(width - 1), 0}, width);
}

const Type& TypeProvider::getScalarType(bitmask<IntegralFlags> flags) const {
    auto ptr = builtins::Builtins::Instance.scalarTypeTable[flags.bits() & 0x7];
    SLANG_ASSERT(ptr);
    return *ptr;
}

} // namespace slang::ast
