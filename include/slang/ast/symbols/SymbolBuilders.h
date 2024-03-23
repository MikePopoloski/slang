//------------------------------------------------------------------------------
//! @file SymbolBuilders.h
//! @brief Contains helpers for constructing symbols programmatically
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"

namespace slang::ast {

class UnpackedStructType;

/// A helper class for constructing method symbols programmatically.
class SLANG_EXPORT MethodBuilder {
public:
    /// The compilation used to construct symbols.
    Compilation& compilation;

    /// The method being constructed.
    SubroutineSymbol& symbol;

    /// Constructs a new method symbol with the given properties.
    MethodBuilder(Compilation& compilation, std::string_view name, const Type& returnType,
                  SubroutineKind kind = SubroutineKind::Function);
    ~MethodBuilder();

    MethodBuilder(const MethodBuilder&) = delete;
    MethodBuilder(MethodBuilder&&) noexcept;

    /// Adds an argument to the method with the given properties. Note that if a
    /// @a defaultValue is provided, the type must be integral.
    FormalArgumentSymbol& addArg(std::string_view name, const Type& type,
                                 ArgumentDirection direction = ArgumentDirection::In,
                                 std::optional<SVInt> defaultValue = {});

    /// Makes a copy of the given argument and adds it to this method.
    FormalArgumentSymbol& copyArg(const FormalArgumentSymbol& fromArg);

    /// Adds flags to the method.
    void addFlags(bitmask<MethodFlags> flags);

    SmallVector<const FormalArgumentSymbol*> args;
};

/// A helper class for constructing class types programmatically.
class SLANG_EXPORT ClassBuilder {
public:
    /// The compilation used to construct symbols.
    Compilation& compilation;

    /// The class type being constructed.
    ClassType& type;

    ClassBuilder(Compilation& compilation, std::string_view name);
    ClassBuilder(Compilation& compilation, ClassType& existing);

    /// Adds a method to the class with the given properties. The returned builder
    /// object can be used to modify the method further.
    MethodBuilder addMethod(std::string_view name, const Type& returnType,
                            SubroutineKind kind = SubroutineKind::Function);
};

/// A helper class for constructing struct types programmatically.
class SLANG_EXPORT StructBuilder {
public:
    /// The compilation used to construct symbols.
    Compilation& compilation;

    /// The struct type being constructed.
    UnpackedStructType& type;

    StructBuilder(const Scope& scope, LookupLocation lookupLocation);

    /// Adds a field to the struct.
    void addField(std::string_view name, const Type& fieldType,
                  bitmask<VariableFlags> flags = VariableFlags::None);

private:
    uint64_t currBitOffset = 0;
    uint32_t currFieldIndex = 0;
};

} // namespace slang::ast
