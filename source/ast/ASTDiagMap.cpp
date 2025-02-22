//------------------------------------------------------------------------------
// ASTDiagMap.cpp
// AST Diagnostic Map
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ASTDiagMap.h"

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/diagnostics/StatementsDiags.h"

namespace slang::ast {

Diagnostic& ASTDiagMap::add(Diagnostic diag, bool& isNew) {
    auto [it, inserted] = map.try_emplace({diag.code, diag.location}, std::vector<Diagnostic>{});
    isNew = inserted;
    it->second.emplace_back(std::move(diag));
    return it->second.back();
}

Diagnostics ASTDiagMap::coalesce(const SourceManager* sourceManager) {
    Diagnostics results;
    for (auto& [key, diagList] : map) {
        // If the location is NoLocation, just issue each diagnostic.
        if (std::get<1>(key) == SourceLocation::NoLocation) {
            for (auto& diag : diagList)
                results.emplace_back(diag);
            continue;
        }

        // Try to find a diagnostic in an instance that isn't at the top-level
        // (printing such a path seems silly).
        const Diagnostic* found = nullptr;
        const Symbol* inst = nullptr;
        size_t count = 0;
        bool differingArgs = false;

        for (auto& diag : diagList) {
            if (found && *found != diag) {
                differingArgs = true;
                break;
            }

            auto symbol = diag.symbol;
            while (symbol && symbol->kind != SymbolKind::InstanceBody) {
                const Scope* scope;
                if (symbol->kind == SymbolKind::CheckerInstanceBody) {
                    auto& checkerBody = symbol->as<CheckerInstanceBodySymbol>();
                    SLANG_ASSERT(checkerBody.parentInstance);
                    scope = checkerBody.parentInstance->getParentScope();

                    // Add an expansion note to the diagnostic since
                    // we won't have added it yet for the checker.
                    if (!checkerBody.flags.has(InstanceFlags::Uninstantiated)) {
                        diag.addNote(diag::NoteWhileExpanding, checkerBody.parentInstance->location)
                            << "checker"sv << checkerBody.checker.name;
                    }
                }
                else {
                    scope = symbol->getParentScope();
                }

                symbol = scope ? &scope->asSymbol() : nullptr;
            }

            if (!symbol)
                continue;

            auto parent = symbol->as<InstanceBodySymbol>().parentInstance;
            SLANG_ASSERT(parent);

            count++;
            if (auto scope = parent->getParentScope()) {
                auto& sym = scope->asSymbol();
                if (sym.kind != SymbolKind::Root && sym.kind != SymbolKind::CompilationUnit) {
                    found = &diag;
                    inst = parent;
                }
            }
        }

        if (!differingArgs && found &&
            inst->as<InstanceSymbol>().getDefinition().getInstanceCount() > count) {
            // The diagnostic is present only in some instances, so include the coalescing
            // information to point the user towards the right ones.
            Diagnostic diag = *found;
            diag.symbol = inst;
            diag.coalesceCount = count;
            results.emplace_back(std::move(diag));
        }
        else {
            // Otherwise no coalescing. If we had differing arguments then set each
            // diagnostic's coalesce count to 1 (as opposed to letting it stay nullopt)
            // so that we get the instance path to it printed automatically.
            auto it = diagList.begin();
            SLANG_ASSERT(it != diagList.end());

            {
                Diagnostic d = *it;
                if (differingArgs)
                    d.coalesceCount = 1;
                results.emplace_back(std::move(d));
            }

            for (++it; it != diagList.end(); ++it) {
                Diagnostic d = *it;
                if (d != results.back()) {
                    if (differingArgs)
                        d.coalesceCount = 1;
                    results.emplace_back(std::move(d));
                }
            }
        }
    }

    if (sourceManager)
        results.sort(*sourceManager);

    return results;
}

} // namespace slang::ast
