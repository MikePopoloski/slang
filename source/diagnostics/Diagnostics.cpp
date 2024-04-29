//------------------------------------------------------------------------------
// Diagnostics.cpp
// Diagnostic tracking and reporting
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/Diagnostics.h"

#include "slang/text/SourceManager.h"

namespace slang {

Diagnostic::Diagnostic() noexcept : location(SourceLocation::NoLocation) {
}

Diagnostic::Diagnostic(DiagCode code, SourceLocation location) noexcept :
    code(code), location(location) {
}

Diagnostic::Diagnostic(const ast::Symbol& source, DiagCode code, SourceLocation location) noexcept :
    code(code), location(location), symbol(&source) {
}

bool Diagnostic::isError() const {
    return getDefaultSeverity(code) >= DiagnosticSeverity::Error;
}

Diagnostic& Diagnostic::addNote(DiagCode noteCode, SourceLocation noteLocation) {
    SLANG_ASSERT(noteLocation);
    notes.emplace_back(noteCode, noteLocation);
    return notes.back();
}

Diagnostic& Diagnostic::addNote(DiagCode noteCode, SourceRange range) {
    return addNote(noteCode, range.start()) << range;
}

Diagnostic& Diagnostic::addNote(const Diagnostic& diag) {
    notes.emplace_back(diag);
    return notes.back();
}

Diagnostic& Diagnostic::addStringAllowEmpty(const std::string& arg) {
    args.emplace_back(arg);
    return *this;
}

Diagnostic& Diagnostic::operator<<(const std::string& arg) {
    SLANG_ASSERT(!arg.empty());
    args.emplace_back(arg);
    return *this;
}

Diagnostic& Diagnostic::operator<<(std::string_view arg) {
    SLANG_ASSERT(!arg.empty());
    args.emplace_back(std::string(arg));
    return *this;
}

Diagnostic& Diagnostic::operator<<(SourceRange range) {
    SLANG_ASSERT(range.start());
    SLANG_ASSERT(range.end());
    ranges.push_back(range);
    return *this;
}

Diagnostic& Diagnostic::operator<<(const ConstantValue& arg) {
    args.emplace_back(arg);
    return *this;
}

Diagnostic& Diagnostic::operator<<(char arg) {
    args.emplace_back(std::string(1, arg));
    return *this;
}

Diagnostic& Diagnostic::operator<<(real_t arg) {
    args.emplace_back(ConstantValue(arg));
    return *this;
}

Diagnostic& Diagnostic::operator<<(shortreal_t arg) {
    args.emplace_back(ConstantValue(arg));
    return *this;
}

bool Diagnostic::operator==(const Diagnostic& rhs) const {
    // NOTE: this method doesn't check every field; we want diagnostics that are
    // "logically" equivalent to return true even if some of the fields actually
    // differ in ways that don't matter.
    if (code != rhs.code || location != rhs.location || args.size() != rhs.args.size())
        return false;

    for (auto lit = args.begin(), rit = rhs.args.begin(); lit != args.end(); lit++, rit++) {
        // Unwrap the argument type (stored as a variant).
        bool result = std::visit(
            [&](auto&& l, auto&& r) {
                using LT = std::decay_t<decltype(l)>;
                using RT = std::decay_t<decltype(r)>;
                if constexpr (std::is_same_v<LT, RT>) {
                    if constexpr (std::is_same_v<Diagnostic::CustomArgType, LT>) {
                        return l.first == r.first;
                    }
                    else {
                        return l == r;
                    }
                }
                else {
                    return false;
                }
            },
            *lit, *rit);

        if (!result)
            return false;
    }

    return true;
}

Diagnostic& Diagnostics::add(DiagCode code, SourceLocation location) {
    SLANG_ASSERT(location);
    emplace_back(code, location);
    return back();
}

Diagnostic& Diagnostics::add(DiagCode code, SourceRange range) {
    return add(code, range.start()) << range;
}

Diagnostic& Diagnostics::add(const ast::Symbol& source, DiagCode code, SourceLocation location) {
    SLANG_ASSERT(location);
    emplace_back(source, code, location);
    return back();
}

Diagnostic& Diagnostics::add(const ast::Symbol& source, DiagCode code, SourceRange range) {
    return add(source, code, range.start()) << range;
}

void Diagnostics::sort(const SourceManager& sourceManager) {
    auto compare = [&sourceManager](auto& x, auto& y) {
        SourceLocation xl = sourceManager.getFullyExpandedLoc(x.location);
        SourceLocation yl = sourceManager.getFullyExpandedLoc(y.location);

        auto xb = sourceManager.getSortKey(xl.buffer());
        auto yb = sourceManager.getSortKey(yl.buffer());
        if (xb < yb)
            return true;
        if (xb == yb) {
            if (xl.offset() < yl.offset())
                return true;
            if (xl == yl)
                return x.code < y.code;
        }
        return false;
    };

    std::ranges::stable_sort(*this, compare);
}

Diagnostics Diagnostics::filter(std::initializer_list<DiagCode> list) const {
    Diagnostics result;
    result.reserve(size());

    for (auto& diag : *this) {
        if (std::ranges::none_of(list, [&](DiagCode code) { return code == diag.code; }))
            result.push_back(diag);
    }

    return result;
}

} // namespace slang
