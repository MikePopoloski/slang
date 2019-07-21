//------------------------------------------------------------------------------
// EvalContext.cpp
// Expression evaluation context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/EvalContext.h"

#include "slang/binding/BindContext.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/TypeSymbols.h"
#include "slang/text/FormatBuffer.h"

namespace slang {

EvalContext::EvalContext(const Scope& scope, bitmask<EvalFlags> flags) :
    rootScope(&scope), flags(flags) {
    stack.emplace_back(Frame{});
}

ConstantValue* EvalContext::createLocal(const ValueSymbol* symbol, ConstantValue value) {
    ConstantValue& result = stack.back().temporaries[symbol];
    ASSERT(!result);

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

void EvalContext::pushFrame(const SubroutineSymbol& subroutine, SourceLocation callLocation,
                            LookupLocation lookupLocation) {
    Frame frame;
    frame.subroutine = &subroutine;
    frame.callLocation = callLocation;
    frame.lookupLocation = lookupLocation;
    stack.emplace_back(std::move(frame));
}

void EvalContext::popFrame() {
    stack.pop_back();
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
    Diagnostic& diag = diags.add(code, location);
    reportStack();
    return diag;
}

Diagnostic& EvalContext::addDiag(DiagCode code, SourceRange range) {
    Diagnostic& diag = diags.add(code, range);
    reportStack();
    return diag;
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

    FormatBuffer buffer;
    for (const Frame& frame : make_reverse_range(stack)) {
        if (!frame.subroutine)
            break;

        if (isVerifying()) {
            diags.add(diag::NoteInCallTo, frame.callLocation) << frame.subroutine->name;
        }
        else {
            buffer.clear();
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
    }
}

} // namespace slang