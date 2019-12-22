//------------------------------------------------------------------------------
// Diagnostics.cpp
// Diagnostic tracking and reporting.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/Diagnostics.h"

#include "slang/symbols/Type.h"
#include "slang/text/SourceManager.h"

namespace slang {

// Defined in the generated DiagCode.cpp file.
DiagnosticSeverity getDefaultSeverity(DiagCode code);

static bool isError(DiagCode code) {
    return getDefaultSeverity(code) >= DiagnosticSeverity::Error;
}

static bool isError(const Diagnostic& diag) {
    return isError(diag.code);
}

Diagnostic::Diagnostic(DiagCode code, SourceLocation location) noexcept :
    code(code), location(location) {
}

Diagnostic::Diagnostic(const Symbol& source, DiagCode code, SourceLocation location) noexcept :
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

Diagnostic& Diagnostic::operator<<(const std::string& arg) {
    args.emplace_back(arg);
    return *this;
}

Diagnostic& Diagnostic::operator<<(string_view arg) {
    args.emplace_back(std::string(arg));
    return *this;
}

Diagnostic& Diagnostic::operator<<(const Type& arg) {
    ASSERT(!arg.isError());
    args.emplace_back(&arg);
    return *this;
}

Diagnostic& Diagnostic::operator<<(SourceRange range) {
    ASSERT(range.start());
    ASSERT(range.end());
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

Diagnostic& Diagnostics::add(DiagCode code, SourceLocation location) {
    if (isError(code))
        errorCount++;

    ASSERT(location);
    emplace(code, location);
    return back();
}

Diagnostic& Diagnostics::add(DiagCode code, SourceRange range) {
    return add(code, range.start()) << range;
}

Diagnostic& Diagnostics::add(const Symbol& source, DiagCode code, SourceLocation location) {
    if (isError(code))
        errorCount++;

    ASSERT(location);
    emplace(source, code, location);
    return back();
}

Diagnostic& Diagnostics::add(const Symbol& source, DiagCode code, SourceRange range) {
    return add(source, code, range.start()) << range;
}

void Diagnostics::append(const Diagnostic& other) {
    if (isError(other))
        errorCount++;

    SmallVectorSized::append(other);
}

void Diagnostics::append(Diagnostic&& other) {
    if (isError(other))
        errorCount++;

    SmallVectorSized::emplace(std::move(other));
}

void Diagnostics::appendRange(const Diagnostics& other) {
    for (auto& diag : other) {
        if (isError(diag))
            errorCount++;
    }

    SmallVectorSized::appendRange(other);
}

void Diagnostics::pop() {
    if (isError(back()))
        errorCount--;

    SmallVectorSized::pop();
}

void Diagnostics::clear() {
    SmallVectorSized::clear();
    errorCount = 0;
}

void Diagnostics::sort(const SourceManager& sourceManager) {
    auto compare = [&sourceManager](auto& x, auto& y) {
        SourceLocation xl = sourceManager.getFullyExpandedLoc(x.location);
        SourceLocation yl = sourceManager.getFullyExpandedLoc(y.location);
        if (xl < yl)
            return true;
        if (xl == yl)
            return x.code < y.code;
        return false;
    };

    std::stable_sort(begin(), end(), compare);
}

} // namespace slang
