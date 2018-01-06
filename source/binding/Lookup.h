//------------------------------------------------------------------------------
// Lookup.h
// Lookup-related definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "diagnostics/Diagnostics.h"
#include "text/SourceLocation.h"
#include "util/Util.h"

namespace slang {

class Scope;
class Symbol;

/// Specifies possible kinds of lookups that can be done.
enum class LookupNameKind {
    /// A lookup of a simple name, starting in the local scope. The lookup location is
    /// used to qualify accessible signals. Imports from packages are considered.
    Local,

    /// The lookup is for the first part of a scoped name. This first performs
    /// the equivalent of a Local lookup; if no symbol is found using that method,
    /// it will search for a package with the given name.
    Scoped,

    /// A lookup for a simple name that is part of a callable expression (task or function).
    /// This has additional rules; specifically, SystemVerilog allows tasks and functions
    /// to be referenced before they are declared.
    Callable,

    /// Names referenced as part of a bind instantiation have special rules. For example,
    /// previously imported wildcard names are visible, but the bind lookup itself will
    /// not cause non-imported wildcard names to become visible even if they match.
    BindTarget
};

/// This type denotes the ordering of symbols within a particular scope,
/// for the purposes of determining whether a found symbol is visible
/// compared to the given reference point. For example, variables cannot
/// be referenced before they are declared.
class LookupContext {
public:
    LookupContext() = default;

    /// Places a reference point just before the given symbol in its parent scope.
    static LookupContext before(const Symbol& symbol);

    /// Places a reference point just after the given symbol in its parent scope.
    static LookupContext after(const Symbol& symbol);

    /// Places a reference point at the start of the given scope.
    static LookupContext startOfScope(const Scope& scope);

    /// Places a reference point at the end of the given scope.
    static LookupContext endOfScope(const Scope& scope);

    /// A special reference point that should always compare after any other reference point.
    static const LookupContext max;

    /// A special reference point that should always compare before any other reference point.
    static const LookupContext min;

    bool operator==(const LookupContext& other) const {
        return scope == other.scope && index == other.index;
    }

    bool operator!=(const LookupContext& other) const { return !(*this == other); }
    bool operator<(const LookupContext& other) const;

private:
    friend class Scope;

    LookupContext(const Scope* scope_, uint32_t index) :
        scope(scope_), index(index) {}

    const Scope* scope = nullptr;
    uint32_t index = 0;
};

class LookupOperation {
public:
    LookupOperation(string_view name, const Scope& scope, SourceRange sourceRange,
                    LookupContext context = LookupContext::max,
                    LookupNameKind nameKind = LookupNameKind::Local);

    bool hasError() const;
    bool wasImported() const { return resultImported; }

    const Diagnostics& getDiagnostics() const { return diagnostics; }

    const Symbol* getResult() const { return found; }

private:
    void doLookup(string_view name, const Scope& scope, SourceRange sourceRange,
                  LookupContext context, LookupNameKind nameKind);

    const Symbol* found = nullptr;
    Diagnostics diagnostics;
    bool resultImported = false;
};

}