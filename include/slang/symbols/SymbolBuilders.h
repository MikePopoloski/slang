//------------------------------------------------------------------------------
//! @file SymbolBuilders.h
//! @brief Contains helpers for constructing symbols programmatically
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/VariableSymbols.h"

namespace slang {

class UnpackedStructType;

/// A helper class for constructing method symbols programmatically.
class MethodBuilder {
public:
    /// The compilation used to construct symbols.
    Compilation& compilation;

    /// The method being constructed.
    SubroutineSymbol& symbol;

    /// Constructs a new method symbol with the given properties.
    MethodBuilder(Compilation& compilation, string_view name, const Type& returnType,
                  SubroutineKind kind = SubroutineKind::Function);
    ~MethodBuilder();

    MethodBuilder(const MethodBuilder&) = delete;
    MethodBuilder(MethodBuilder&&) noexcept;

    /// Adds an argument to the method with the given properties. Note that if a
    /// @a defaultValue is provided, the type must be integral.
    FormalArgumentSymbol& addArg(string_view name, const Type& type,
                                 ArgumentDirection direction = ArgumentDirection::In,
                                 optional<SVInt> defaultValue = {});

    /// Makes a copy of the given argument and adds it to this method.
    FormalArgumentSymbol& copyArg(const FormalArgumentSymbol& fromArg);

    /// Adds flags to the method.
    void addFlags(bitmask<MethodFlags> flags);

private:
    SmallVectorSized<const FormalArgumentSymbol*, 4> args;
};

/// A helper class for constructing class types programmatically.
class ClassBuilder {
public:
    /// The compilation used to construct symbols.
    Compilation& compilation;

    /// The class type being constructed.
    ClassType& type;

    ClassBuilder(Compilation& compilation, string_view name);
    ClassBuilder(Compilation& compilation, ClassType& existing);

    /// Adds a method to the class with the given properties. The returned builder
    /// object can be used to modify the method further.
    MethodBuilder addMethod(string_view name, const Type& returnType,
                            SubroutineKind kind = SubroutineKind::Function);
};

/// A helper class for constructing struct types programmatically.
class StructBuilder {
public:
    /// The compilation used to construct symbols.
    Compilation& compilation;

    /// The struct type being constructed.
    UnpackedStructType& type;

    StructBuilder(const Scope& scope, LookupLocation lookupLocation);

    /// Adds a field to the struct.
    void addField(string_view name, const Type& fieldType,
                  bitmask<VariableFlags> flags = VariableFlags::None);

    /// Adds a field to the struct, linking its type to the given declared type.
    void addField(string_view name, const DeclaredType& typeLink,
                  bitmask<VariableFlags> flags = VariableFlags::None);

private:
    uint32_t currFieldIndex = 0;
};

} // namespace slang
