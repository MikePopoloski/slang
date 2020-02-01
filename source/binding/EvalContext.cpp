//------------------------------------------------------------------------------
// EvalContext.cpp
// Expression evaluation context
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/EvalContext.h"

#include "../text/FormatBuffer.h"

#include "slang/binding/BindContext.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"

namespace slang {

EvalContext::EvalContext(const Scope& scope, bitmask<EvalFlags> flags) :
    flags(flags), rootScope(&scope) {
    stack.emplace(Frame{});
}

ConstantValue* EvalContext::createLocal(const ValueSymbol* symbol, ConstantValue value) {
    ConstantValue& result = stack.back().temporaries[symbol];
    if (!value)
        result = symbol->getType().getDefaultValue();
    else {
        ASSERT(!value.isInteger() ||
               value.integer().getBitWidth() == symbol->getType().getBitWidth());

        result = std::move(value);
    }

    return &result;
}

ConstantValue* EvalContext::findLocal(const ValueSymbol* symbol) {
    auto it = stack.back().temporaries.find(symbol);
    if (it == stack.back().temporaries.end())
        return nullptr;
    return &it->second;
}

bool EvalContext::pushFrame(const SubroutineSymbol& subroutine, SourceLocation callLocation,
                            LookupLocation lookupLocation) {
    const uint32_t maxDepth = rootScope->getCompilation().getOptions().maxConstexprDepth;
    if (stack.size() >= maxDepth) {
        addDiag(diag::NoteExceededMaxCallDepth, subroutine.location) << maxDepth;
        return false;
    }

    Frame frame;
    frame.subroutine = &subroutine;
    frame.callLocation = callLocation;
    frame.lookupLocation = lookupLocation;
    stack.emplace(std::move(frame));
    return true;
}

void EvalContext::popFrame() {
    stack.pop();
}

bool EvalContext::step(SourceLocation loc) {
    if (++steps < rootScope->getCompilation().getOptions().maxConstexprSteps)
        return true;

    addDiag(diag::NoteExceededMaxSteps, loc);
    return false;
}

const Scope& EvalContext::getCurrentScope() const {
    const Frame& frame = topFrame();
    if (frame.subroutine)
        return *frame.subroutine;
    return getRootScope();
}

std::string EvalContext::dumpStack() const {
    FormatBuffer buffer;
    int index = 0;
    for (const Frame& frame : stack) {
        buffer.format("{}: {}\n", index++, frame.subroutine ? frame.subroutine->name : "<global>");
        for (auto& [symbol, value] : frame.temporaries)
            buffer.format("    {} = {}\n", symbol->name, value.toString());
    }
    return buffer.str();
}

Diagnostic& EvalContext::addDiag(DiagCode code, SourceLocation location) {
    // Be careful: adding diagnostics can resize the underlying array,
    // so we have to remember an index here and return the reference
    // after reporting the stack.
    size_t index = diags.size();
    diags.add(code, location);
    reportStack();
    return diags[index];
}

Diagnostic& EvalContext::addDiag(DiagCode code, SourceRange range) {
    size_t index = diags.size();
    diags.add(code, range);
    reportStack();
    return diags[index];
}

void EvalContext::addDiags(const Diagnostics& additional) {
    reportStack();
    diags.appendRange(additional);
}

void EvalContext::reportDiags(const BindContext& context, SourceRange range) const {
    if (!diags.empty()) {
        Diagnostic& diag = context.addDiag(diag::ExpressionNotConstant, range);
        for (const Diagnostic& note : diags)
            diag.addNote(note);
    }
}

void EvalContext::reportStack() {
    // Once per evaluation, include the current callstack in the list of
    // diagnostics if we end up issuing any at all.
    if (std::exchange(reportedCallstack, true))
        return;

    reportStack(diags);
}

static void reportFrame(const EvalContext& context, Diagnostics& diags,
                        const EvalContext::Frame& frame) {
    if (!frame.subroutine)
        return;

    if (context.isVerifying()) {
        diags.add(diag::NoteInCallTo, frame.callLocation) << frame.subroutine->name;
        return;
    }

    FormatBuffer buffer;
    buffer.format("{}(", frame.subroutine->name);

    for (auto arg : frame.subroutine->arguments) {
        auto it = frame.temporaries.find(arg);
        ASSERT(it != frame.temporaries.end());

        buffer.append(it->second.toString());
        if (arg != frame.subroutine->arguments.last(1)[0])
            buffer.append(", ");
    }

    buffer.append(")");

    diags.add(diag::NoteInCallTo, frame.callLocation) << buffer.str();
}

void EvalContext::reportStack(Diagnostics& stackDiags) const {
    const size_t limit = rootScope->getCompilation().getOptions().maxConstexprBacktrace;
    if (stack.size() <= limit || limit == 0) {
        FormatBuffer buffer;
        for (const Frame& frame : make_reverse_range(stack))
            reportFrame(*this, stackDiags, frame);
        return;
    }

    const ptrdiff_t start = ptrdiff_t(limit / 2);
    const ptrdiff_t end = start + ptrdiff_t(limit % 2);
    auto reversed = make_reverse_range(stack);
    for (auto it = reversed.begin(), itEnd = it + start; it != itEnd; it++)
        reportFrame(*this, stackDiags, *it);

    stackDiags.add(diag::NoteSkippingFrames, (reversed.begin() + start)->callLocation)
        << stack.size() - limit;

    for (auto it = reversed.end() - end, itEnd = reversed.end(); it != itEnd; it++)
        reportFrame(*this, stackDiags, *it);
}

} // namespace slang