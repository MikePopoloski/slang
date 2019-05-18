//------------------------------------------------------------------------------
// Diagnostics.cpp
// Diagnostic tracking and reporting.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/Diagnostics.h"

#include "slang/symbols/HierarchySymbols.h"
#include "slang/text/SourceManager.h"

namespace slang {

Diagnostic::Diagnostic(DiagCode code, SourceLocation location) : code(code), location(location) {
}

Diagnostic::Diagnostic(const Symbol& source, DiagCode code, SourceLocation location) :
    code(code), location(location), symbol(&source) {
}

Diagnostic& Diagnostic::addNote(DiagCode noteCode, SourceLocation noteLocation) {
    ASSERT(noteLocation);
    notes.emplace_back(noteCode, noteLocation);
    return notes.back();
}

Diagnostic& Diagnostic::addNote(const Diagnostic& diag) {
    notes.emplace_back(diag);
    return notes.back();
}

bool Diagnostic::isSuppressed() const {
    const Symbol* sym = symbol;
    while (sym) {
        if (sym->kind == SymbolKind::GenerateBlock &&
            !sym->as<GenerateBlockSymbol>().isInstantiated)
            return true;

        auto scope = sym->getScope();
        sym = scope ? &scope->asSymbol() : nullptr;
    }
    return false;
}

Diagnostic& operator<<(Diagnostic& diag, const std::string& arg) {
    diag.args.emplace_back(arg);
    return diag;
}

Diagnostic& operator<<(Diagnostic& diag, string_view arg) {
    diag.args.emplace_back(std::string(arg));
    return diag;
}

Diagnostic& operator<<(Diagnostic& diag, const Type& arg) {
    diag.args.emplace_back(&arg);
    return diag;
}

Diagnostic& operator<<(Diagnostic& diag, SourceRange range) {
    ASSERT(range.start());
    ASSERT(range.end());
    diag.ranges.push_back(range);
    return diag;
}

Diagnostic& operator<<(Diagnostic& diag, const ConstantValue& arg) {
    diag.args.emplace_back(arg);
    return diag;
}

Diagnostic& Diagnostics::add(DiagCode code, SourceLocation location) {
    ASSERT(location);
    emplace(code, location);
    return back();
}

Diagnostic& Diagnostics::add(DiagCode code, SourceRange range) {
    return add(code, range.start()) << range;
}

Diagnostic& Diagnostics::add(const Symbol& source, DiagCode code, SourceLocation location) {
    ASSERT(location);
    emplace(source, code, location);
    return back();
}

Diagnostic& Diagnostics::add(const Symbol& source, DiagCode code, SourceRange range) {
    return add(source, code, range.start()) << range;
}

void Diagnostics::sort(const SourceManager& sourceManager) {
    auto compare = [&sourceManager](auto& x, auto& y) {
        SourceLocation xl = sourceManager.getFullyExpandedLoc(x.location);
        SourceLocation yl = sourceManager.getFullyExpandedLoc(y.location);
        return xl < yl;
    };

    std::stable_sort(begin(), end(), compare);
}

} // namespace slang
