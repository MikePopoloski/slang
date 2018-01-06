//------------------------------------------------------------------------------
// Lookup.cpp
// Lookup-related definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Lookup.h"

#include "symbols/Scope.h"
#include "symbols/HierarchySymbols.h"
#include "symbols/MemberSymbols.h"

namespace slang {

const LookupContext LookupContext::max{ nullptr, UINT_MAX };
const LookupContext LookupContext::min{ nullptr, 0 };

LookupContext LookupContext::before(const Symbol& symbol) {
    return LookupContext(symbol.getScope(), (uint32_t)symbol.getIndex());
}

LookupContext LookupContext::after(const Symbol& symbol) {
    return LookupContext(symbol.getScope(), (uint32_t)symbol.getIndex() + 1);
}

LookupContext LookupContext::startOfScope(const Scope& scope) {
    return LookupContext(&scope, 0);
}

LookupContext LookupContext::endOfScope(const Scope& scope) {
    return LookupContext(&scope, UINT32_MAX);
}

bool LookupContext::operator<(const LookupContext& other) const {
    return index < other.index;
}

LookupOperation::LookupOperation(string_view name, const Scope& scope, SourceRange sourceRange,
                                 LookupContext context, LookupNameKind nameKind) {
    doLookup(name, scope, sourceRange, context, nameKind);
}

bool LookupOperation::hasError() const {
    // We have an error if we have any diagnostics or if there was a missing explicit import.
    return !diagnostics.empty() || (!found && resultImported);
}

void LookupOperation::doLookup(string_view name, const Scope& scope, SourceRange sourceRange,
                               LookupContext context, LookupNameKind nameKind) {
    // Try a simple name lookup to see if we find anything.
    SourceLocation location = sourceRange.start();
    const Symbol* symbol = scope.find(name);
    if (symbol) {
        // If the lookup is for a local name, check that we can access the symbol (it must be
        // declared before use). Callables and block names can be referenced anywhere in the scope,
        // so the location doesn't matter for them.
        bool locationGood = true;
        if (nameKind == LookupNameKind::Local)
            locationGood = LookupContext::before(*symbol) < context;

        if (locationGood) {
            // Unwrap the symbol if it's hidden behind an import or hoisted enum member.
            switch (symbol->kind) {
                case SymbolKind::ExplicitImport:
                    found = symbol->as<ExplicitImportSymbol>().importedSymbol();
                    resultImported = true;
                    break;
                case SymbolKind::TransparentMember:
                    found = &symbol->as<TransparentMemberSymbol>().wrapped;
                    break;
                default:
                    found = symbol;
                    break;
            }
            return;
        }
    }

    // Look through any wildcard imports prior to the lookup point and see if their packages
    // contain the name we're looking for.
    struct Import {
        const Symbol* imported;
        const WildcardImportSymbol* import;
    };
    SmallVectorSized<Import, 8> imports;

    for (auto import : scope.getImports()) {
        if (context < LookupContext::after(*import))
            break;

        auto package = import->getPackage();
        if (!package)
            continue;

        const Symbol* imported = package->find(name);
        if (imported)
            imports.emplace(Import { imported, import });
    }

    if (!imports.empty()) {
        if (imports.size() > 1) {
            diagnostics.add(DiagCode::AmbiguousWildcardImport, sourceRange) << name;
            for (const auto& pair : imports) {
                diagnostics.add(DiagCode::NoteImportedFrom, pair.import->location);
                diagnostics.add(DiagCode::NoteDeclarationHere, pair.imported->location);
            }
            return;
        }

        if (symbol) {
            diagnostics.add(DiagCode::ImportNameCollision, sourceRange) << name;
            diagnostics.add(DiagCode::NoteDeclarationHere, symbol->location);
            diagnostics.add(DiagCode::NoteImportedFrom, imports[0].import->location);
            diagnostics.add(DiagCode::NoteDeclarationHere, imports[0].imported->location);
        }

        resultImported = true;
        found = imports[0].imported;
        return;
    }

    // Continue up the scope chain via our parent.
    auto nextScope = scope.getParent();
    if (!nextScope)
        return;

    context = LookupContext::after(scope.asSymbol());
    return doLookup(name, *nextScope, sourceRange, context, nameKind);
}

}