//------------------------------------------------------------------------------
//! @file Diagnostics.h
//! @brief Diagnostic definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <any>
#include <string>
#include <variant>
#include <vector>

#include "slang/numeric/ConstantValue.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Enum.h"
#include "slang/util/SmallVector.h"

namespace slang {

class SourceManager;
class Symbol;

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
    x(Meta)
ENUM_SIZED(DiagSubsystem, uint16_t, DS)
#undef DS

/// The severity of a given diagnostic. This is not tied to the diagnostic itself;
/// it can be configured on a per-diagnostic basis at runtime.
#define DS(x) \
    x(Ignored) \
    x(Note) \
    x(Warning) \
    x(Error) \
    x(Fatal)
ENUM(DiagnosticSeverity, DS)
// clang-format on

class DiagCode {
public:
    constexpr DiagCode() : subsystem(DiagSubsystem::Invalid), code(0) {}
    constexpr DiagCode(DiagSubsystem subsystem, uint16_t code) : subsystem(subsystem), code(code) {}

    constexpr DiagSubsystem getSubsystem() const { return subsystem; }
    constexpr uint16_t getCode() const { return code; }

    constexpr bool valid() const { return subsystem != DiagSubsystem::Invalid; }

    constexpr explicit operator bool() const { return valid(); }

    constexpr bool operator==(DiagCode other) const {
        return subsystem == other.subsystem && code == other.code;
    }

    constexpr bool operator!=(DiagCode other) const { return !(*this == other); }

    constexpr bool operator<(DiagCode other) const { return code < other.code; }

    static const span<const DiagCode> KnownCodes;

private:
    DiagSubsystem subsystem;
    uint16_t code;
};

std::ostream& operator<<(std::ostream& os, DiagCode code);
string_view toString(DiagCode code);

/// Wraps up a reported diagnostic along with location in source and any arguments.
class Diagnostic {
public:
    // Diagnostic-specific arguments that can be used to better report messages.
    using Arg = std::variant<std::string, int64_t, uint64_t, char, ConstantValue, std::any>;
    std::vector<Arg> args;
    std::vector<SourceRange> ranges;
    std::vector<Diagnostic> notes;
    optional<size_t> coalesceCount;

    /// The specific kind of diagnostic that was issued.
    DiagCode code;

    /// The location in source of the cause of the diagnostic.
    SourceLocation location;

    /// The symbol in which the diagnostic occurred, or null if not applicable.
    const Symbol* symbol = nullptr;

    /// Constructs a new Diagnostic entry with the given code and location.
    Diagnostic(DiagCode code, SourceLocation location) noexcept;

    /// Constructs a new Diagnostic entry with the given symbol, code and location.
    Diagnostic(const Symbol& source, DiagCode code, SourceLocation location) noexcept;

    /// Returns true if this diagnostic's code is intrinsically considered an error,
    /// regardless of what severity mapping rules might be in place.
    bool isError() const;

    /// Adds a new note to the diagnostic at the given source location.
    Diagnostic& addNote(DiagCode code, SourceLocation location);
    Diagnostic& addNote(DiagCode code, SourceRange range);
    Diagnostic& addNote(const Diagnostic& diag);

    /// Adds an argument to the diagnostic.
    Diagnostic& operator<<(const std::string& arg);
    Diagnostic& operator<<(string_view arg);
    Diagnostic& operator<<(SourceRange arg);
    Diagnostic& operator<<(const ConstantValue& arg);
    Diagnostic& operator<<(char arg);
    Diagnostic& operator<<(real_t arg);
    Diagnostic& operator<<(shortreal_t arg);

    Diagnostic& addStringAllowEmpty(const std::string& arg);

    template<typename T, typename = std::enable_if_t<std::is_integral_v<T> && std::is_signed_v<T>>>
    Diagnostic& operator<<(T arg) {
        args.emplace_back((int64_t)arg);
        return *this;
    }

    template<typename T, typename = void,
             typename = std::enable_if_t<std::is_integral_v<T> && std::is_unsigned_v<T>>>
    Diagnostic& operator<<(T arg) {
        args.emplace_back((uint64_t)arg);
        return *this;
    }

    bool operator==(const Diagnostic& rhs) const;
    bool operator!=(const Diagnostic& rhs) const { return !(*this == rhs); }
};

/// A collection of diagnostics.
class Diagnostics : public SmallVectorSized<Diagnostic, 2> {
public:
    Diagnostics() = default;
    Diagnostics(Diagnostics&& other) noexcept = default;

    /// Adds a new diagnostic to the collection, pointing to the given source location.
    Diagnostic& add(DiagCode code, SourceLocation location);

    /// Adds a new diagnostic to the collection, highlighting the given source range.
    Diagnostic& add(DiagCode code, SourceRange range);

    /// Adds a new diagnostic to the collection, pointing to the given source location.
    Diagnostic& add(const Symbol& source, DiagCode code, SourceLocation location);

    /// Adds a new diagnostic to the collection, highlighting the given source range.
    Diagnostic& add(const Symbol& source, DiagCode code, SourceRange range);

    /// Sorts the diagnostics in the collection based on source file and line number.
    void sort(const SourceManager& sourceManager);
};

class DiagGroup {
public:
    explicit DiagGroup(const std::string& name, const std::vector<DiagCode>& diags) :
        name(name), diags(diags) {}

    string_view getName() const { return name; }
    span<const DiagCode> getDiags() const { return diags; }

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
