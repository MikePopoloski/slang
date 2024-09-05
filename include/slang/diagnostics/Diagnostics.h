//------------------------------------------------------------------------------
//! @file Diagnostics.h
//! @brief Diagnostic definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <any>
#include <concepts>
#include <string>
#include <typeindex>
#include <variant>
#include <vector>

#include "slang/numeric/ConstantValue.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Enum.h"
#include "slang/util/SmallVector.h"
#include "slang/util/TypeTraits.h"

namespace slang {

class SourceManager;

namespace ast {
class Symbol;
}

// clang-format off
#define DS(x) \
    x(Invalid) \
    x(General) \
    x(Lexer) \
    x(Numeric) \
    x(Preprocessor) \
    x(Parser) \
    x(Declarations) \
    x(Expressions) \
    x(Statements) \
    x(Types) \
    x(Lookup) \
    x(SysFuncs) \
    x(ConstEval) \
    x(Compilation) \
    x(Meta) \
    x(Tidy) \
    x(Netlist)
SLANG_ENUM_SIZED(DiagSubsystem, uint16_t, DS)
#undef DS

/// The severity of a given diagnostic. This is not tied to the diagnostic itself;
/// it can be configured on a per-diagnostic basis at runtime.
#define DS(x) \
    x(Ignored) \
    x(Note) \
    x(Warning) \
    x(Error) \
    x(Fatal)
SLANG_ENUM(DiagnosticSeverity, DS)
#undef DS
// clang-format on

/// @brief A compact code that represents a diagnostic.
///
/// Diagnostics are messages issued to users in the form of notes,
/// warnings, or errors. DiagCodes are partitioned into subystems
/// to help keep unrelated diagnostics separated from each other.
class SLANG_EXPORT DiagCode {
public:
    /// Default constructor, object will return false for @a valid
    constexpr DiagCode() : subsystem(DiagSubsystem::Invalid), code(0) {}

    /// Constructs a new DiagCode with the given subsystem and code number.
    constexpr DiagCode(DiagSubsystem subsystem, uint16_t code) : subsystem(subsystem), code(code) {}

    /// Gets the subsystem with which this DiagCode is associated.
    constexpr DiagSubsystem getSubsystem() const { return subsystem; }

    /// Gets the raw numeric code of this DiagCode, unique within its subsystem.
    constexpr uint16_t getCode() const { return code; }

    /// @brief Checks whether the DiagCode is valid.
    ///
    /// Any DiagCode with a subsystem of DiagSubsystem::Invalid will return false,
    /// (which is true for a default constructed DiagCode object).
    constexpr bool valid() const { return subsystem != DiagSubsystem::Invalid; }

    /// Explicit boolean conversion operator that defers to @a valid
    constexpr explicit operator bool() const { return valid(); }

    /// Three way comparison.
    constexpr friend auto operator<=>(DiagCode left, DiagCode right) = default;

    /// @brief A list of all "known" DiagCodes.
    ///
    /// Known codes are ones baked into the library by the diagnostic_gen.py tool.
    static const std::span<const DiagCode> KnownCodes;

private:
    DiagSubsystem subsystem;
    uint16_t code;
};

// Defined in the generated DiagCode.cpp file.
DiagnosticSeverity getDefaultSeverity(DiagCode code);

SLANG_EXPORT std::ostream& operator<<(std::ostream& os, DiagCode code);
SLANG_EXPORT std::string_view toString(DiagCode code);

/// Wraps up a reported diagnostic along with location in source and any arguments.
class SLANG_EXPORT Diagnostic {
public:
    using CustomArgType = std::pair<SLANG_TYPEINDEX, std::any>;

    // Diagnostic-specific arguments that can be used to better report messages.
    using Arg = std::variant<std::string, int64_t, uint64_t, char, ConstantValue, CustomArgType>;
    std::vector<Arg> args;
    std::vector<SourceRange> ranges;
    std::vector<Diagnostic> notes;
    std::optional<size_t> coalesceCount;

    /// The specific kind of diagnostic that was issued.
    DiagCode code;

    /// The location in source of the cause of the diagnostic.
    SourceLocation location;

    /// The symbol in which the diagnostic occurred, or null if not applicable.
    const ast::Symbol* symbol = nullptr;

    /// Default constructs a new Diagnostic entry.
    Diagnostic() noexcept;

    /// Constructs a new Diagnostic entry with the given code and location.
    Diagnostic(DiagCode code, SourceLocation location) noexcept;

    /// Constructs a new Diagnostic entry with the given symbol, code and location.
    Diagnostic(const ast::Symbol& source, DiagCode code, SourceLocation location) noexcept;

    /// Returns true if this diagnostic's code is intrinsically considered an error,
    /// regardless of what severity mapping rules might be in place.
    bool isError() const;

    /// Adds a new note to the diagnostic at the given source location.
    Diagnostic& addNote(DiagCode code, SourceLocation location);
    Diagnostic& addNote(DiagCode code, SourceRange range);
    Diagnostic& addNote(const Diagnostic& diag);

    /// Adds an argument to the diagnostic.
    Diagnostic& operator<<(const std::string& arg);
    Diagnostic& operator<<(std::string_view arg);
    Diagnostic& operator<<(SourceRange arg);
    Diagnostic& operator<<(const ConstantValue& arg);
    Diagnostic& operator<<(char arg);
    Diagnostic& operator<<(real_t arg);
    Diagnostic& operator<<(shortreal_t arg);

    Diagnostic& addStringAllowEmpty(const std::string& arg);

    template<std::signed_integral T>
    Diagnostic& operator<<(T arg) {
        args.emplace_back((int64_t)arg);
        return *this;
    }

    template<std::unsigned_integral T>
    Diagnostic& operator<<(T arg) {
        args.emplace_back((uint64_t)arg);
        return *this;
    }

    bool operator==(const Diagnostic& rhs) const;
};

/// A collection of diagnostics.
class SLANG_EXPORT Diagnostics : public SmallVector<Diagnostic> {
public:
    /// Adds a new diagnostic to the collection, pointing to the given source location.
    Diagnostic& add(DiagCode code, SourceLocation location);

    /// Adds a new diagnostic to the collection, highlighting the given source range.
    Diagnostic& add(DiagCode code, SourceRange range);

    /// Adds a new diagnostic to the collection, pointing to the given source location.
    Diagnostic& add(const ast::Symbol& source, DiagCode code, SourceLocation location);

    /// Adds a new diagnostic to the collection, highlighting the given source range.
    Diagnostic& add(const ast::Symbol& source, DiagCode code, SourceRange range);

    /// Sorts the diagnostics in the collection based on source file and line number.
    void sort(const SourceManager& sourceManager);

    /// Returns a copy of this collection with all diagnostics that match any of
    /// the codes given in @a list filtered out.
    Diagnostics filter(std::initializer_list<DiagCode> list) const;
};

class SLANG_EXPORT DiagGroup {
public:
    explicit DiagGroup(const std::string& name, const std::vector<DiagCode>& diags) :
        name(name), diags(diags) {}

    std::string_view getName() const { return name; }
    std::span<const DiagCode> getDiags() const { return diags; }

private:
    std::string name;
    std::vector<DiagCode> diags;
};

} // namespace slang

namespace std {

template<>
struct hash<slang::DiagCode> {
    size_t operator()(const slang::DiagCode& dc) const {
        return (((size_t)dc.getSubsystem()) << 16) | dc.getCode();
    }
};

} // namespace std

// General diagnostics are used all over, so just include them globally here.
#include "slang/diagnostics/GeneralDiags.h"
