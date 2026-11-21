//------------------------------------------------------------------------------
// ASTDiagMap.cpp
// AST Diagnostic Map
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ASTDiagMap.h"

#include "slang/ast/symbols/CheckerSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/diagnostics/GeneralDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/util/SmallVector.h"

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

        // Diagnostics issued from within sequence / property / let expansions
        // can share a location (e.g. the formal argument reference within the
        // declaration body) even though they come from different instantiations
        // with different actual arguments, so split them up by expansion chain.
        // A diagnostic whose chain extends a shorter one we've already seen
        // is folded into that group, since it means the problem exists in the
        // shared outer declaration regardless of how it's instantiated.
        auto isExpansionNote = [](const Diagnostic& note) {
            return note.code == diag::NoteWhileExpanding || note.code == diag::NoteExpandedHere;
        };

        if (diagList.size() == 1 || std::ranges::none_of(diagList, [&](auto& diag) {
                return std::ranges::any_of(diag.notes, isExpansionNote);
            })) {
            // Common case: no splitting needed.
            coalesceGroup(results, std::get<0>(key), diagList);
            continue;
        }

        std::vector<std::pair<SmallVector<SourceLocation>, const Diagnostic*>> chains;
        for (auto& diag : diagList) {
            auto& [chain, _] = chains.emplace_back(SmallVector<SourceLocation>{}, &diag);
            for (auto& note : diag.notes) {
                if (isExpansionNote(note))
                    chain.push_back(note.location);
            }
        }

        std::ranges::stable_sort(chains, {}, [](auto& c) { return c.first.size(); });

        SmallVector<std::pair<std::span<const SourceLocation>, SmallVector<const Diagnostic*>>>
            groups;
        for (auto& [chain, diag] : chains) {
            auto it = std::ranges::find_if(groups, [&](auto& g) {
                return std::ranges::equal(g.first, std::span(chain).first(g.first.size()));
            });

            if (it == groups.end())
                it = &groups.emplace_back(chain, SmallVector<const Diagnostic*>{});
            it->second.push_back(diag);
        }

        if (groups.size() == 1) {
            coalesceGroup(results, std::get<0>(key), diagList);
        }
        else {
            for (auto& [_, group] : groups) {
                std::vector<Diagnostic> groupDiags;
                groupDiags.reserve(group.size());
                for (auto diag : group)
                    groupDiags.push_back(*diag);
                coalesceGroup(results, std::get<0>(key), groupDiags);
            }
        }
    }

    if (sourceManager)
        results.sort(*sourceManager);

    return results;
}

void ASTDiagMap::coalesceGroup(Diagnostics& results, DiagCode code,
                               std::vector<Diagnostic>& diagList) {
    // Try to find a diagnostic in an instance that isn't at the top-level
    // (printing such a path seems silly).
    const Diagnostic* found = nullptr;
    const Symbol* inst = nullptr;
    size_t count = 0;
    bool differingArgs = false;
    const bool checkDifferentArgs = !code.coalesceWithDifferingArgs();

    for (auto& diag : diagList) {
        if (found && checkDifferentArgs && *found != diag) {
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

        auto& body = symbol->as<InstanceBodySymbol>();
        auto parent = body.parentInstance;
        SLANG_ASSERT(parent);

        // Instances that reused this body from the instance cache
        // also have this diagnostic.
        count += 1 + body.getNumCachedReuses();
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
            if (checkDifferentArgs && d != results.back()) {
                if (differingArgs)
                    d.coalesceCount = 1;
                results.emplace_back(std::move(d));
            }
        }
    }
}

} // namespace slang::ast
