//------------------------------------------------------------------------------
// PyVisitors.h
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "pyslang.h"

#include "slang/ast/ASTVisitor.h"

enum class VisitAction {
    Advance,
    Skip,
    Interrupt,
};

template<typename TDerived, template<class, auto...> class BaseVisitor, auto... baseArgs>
struct PyVisitorBase : public BaseVisitor<TDerived, baseArgs...> {
    py::object f;
    bool interrupted = false;

    static inline constexpr auto doc =
        "Visit a pyslang object with a callback f.\n\n"
        "If f ever returns pyslang.VisitAction.Interrupt, the visit is aborted, "
        "and no additional nodes are visited. If f returns pyslang.VisitAction.Skip, "
        "then no child nodes of the current node are visited, but otherwise the "
        "visit continues. Any other return value, including "
        "pslang.VisitAction.Advance is ignored, and the walk continues.";

    explicit PyVisitorBase(py::object f) : f{f} {}

    template<typename T>
    void handle(const T& t) {
        if (this->interrupted)
            return;
        py::object result = this->f(&t);
        if (result.equal(py::cast(VisitAction::Interrupt))) {
            this->interrupted = true;
            return;
        }
        if (result.not_equal(py::cast(VisitAction::Skip)))
            this->visitDefault(t);
    }
};

struct PyASTVisitor : PyVisitorBase<PyASTVisitor, ASTVisitor, true, true> {
    using PyVisitorBase::PyVisitorBase;
};

template<typename T>
void pyASTVisit(const T& t, py::object f) {
    PyASTVisitor visitor{f};
    t.visit(visitor);
}
