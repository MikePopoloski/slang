//------------------------------------------------------------------------------
// Lookup.cpp
// Contains symbol lookup-related definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/Lookup.h"

#include "slang/symbols/DefinitionSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"

namespace slang {

const LookupLocation LookupLocation::max{ nullptr, UINT_MAX };
const LookupLocation LookupLocation::min{ nullptr, 0 };

LookupLocation LookupLocation::before(const Symbol& symbol) {
    return LookupLocation(symbol.getParentScope(), (uint32_t)symbol.getIndex());
}

LookupLocation LookupLocation::after(const Symbol& symbol) {
    return LookupLocation(symbol.getParentScope(), (uint32_t)symbol.getIndex() + 1);
}

LookupLocation LookupLocation::beforeLexical(const Symbol& symbol) {
    if (InstanceSymbol::isKind(symbol.kind)) {
        auto& def = symbol.as<InstanceSymbol>().definition;
        return LookupLocation(def.getParentScope(), (uint32_t)def.getIndex() + 1);
    }
    return LookupLocation(symbol.getParentScope(), (uint32_t)symbol.getIndex() + 1);
}

bool LookupLocation::operator<(const LookupLocation& other) const {
    ASSERT(scope == other.scope || !scope || !other.scope);
    return index < other.index;
}

Diagnostic& LookupResult::addDiag(const Scope& scope, DiagCode code, SourceLocation location) {
    return diagnostics.add(scope.asSymbol(), code, location);
}

Diagnostic& LookupResult::addDiag(const Scope& scope, DiagCode code, SourceRange sourceRange) {
    return diagnostics.add(scope.asSymbol(), code, sourceRange);
}

bool LookupResult::hasError() const {
    // We have an error if we have any diagnostics or if there was a missing explicit import.
    return !diagnostics.empty() || (!found && wasImported);
}

void LookupResult::clear() {
    found = nullptr;
    systemSubroutine = nullptr;
    wasImported = false;
    isHierarchical = false;
    sawBadImport = false;
    selectors.clear();
    diagnostics.clear();
}

void LookupResult::copyFrom(const LookupResult& other) {
    found = other.found;
    systemSubroutine = other.systemSubroutine;
    wasImported = other.wasImported;
    isHierarchical = other.isHierarchical;
    sawBadImport = other.sawBadImport;

    selectors.clear();
    selectors.appendRange(other.selectors);

    diagnostics.clear();
    diagnostics.appendRange(other.diagnostics);
}

} // namespace slang