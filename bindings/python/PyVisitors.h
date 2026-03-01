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
    std::optional<py::dict> lookup_table;
    bool interrupted = false;

    static inline constexpr auto doc =
        "Visit a pyslang object with a callback function `f` or a `lookup_table` dict.\n\n"
        "At least one of `f` or `lookup_table` must be provided (both default to `None`). "
        "If both are provided, 'lookup_table' will be used to decide which callback to use.\n\n"
        "When `f` is provided without `lookup_table`, it is called for every node visited. "
        "The callback should take a single argument (the current node). "
        "Its return value controls traversal: `pyslang.VisitAction.Interrupt` aborts the "
        "visit, `pyslang.VisitAction.Skip` skips child nodes, and any other return value "
        "(including `pyslang.VisitAction.Advance` or `None`) continues normally.\n\n"
        "When `lookup_table` is provided, it should be a dict mapping node kind enum values "
        "to handler functions. The C++ side checks each node's kind before crossing the "
        "Python boundary, calling only the matching handler. Nodes not in the table are "
        "traversed without invoking Python. `f` is not called in this mode.";

    explicit PyVisitorBase(py::object f, std::optional<py::dict> lt = std::nullopt) :
        f{f}, lookup_table{std::move(lt)} {}

    template<typename T>
    void handle(const T& t) {
        if (this->interrupted)
            return;

        py::object result;
        if (this->lookup_table) {
            // Lookup table filtering
            if constexpr (requires { t.kind; }) {
                auto kind_py = py::cast(t.kind);
                if (!this->lookup_table->contains(kind_py)) {
                    this->visitDefault(t);
                    return;
                }
                py::object handler{(*this->lookup_table)[kind_py]};
                result = handler(&t);
            }
            else {
                this->visitDefault(t);
                return;
            }
        }
        else {
            result = this->f(&t);
        }

        if (result.equal(py::cast(VisitAction::Interrupt))) {
            this->interrupted = true;
            return;
        }
        if (result.not_equal(py::cast(VisitAction::Skip)))
            this->visitDefault(t);
    }
};

struct PyASTVisitor : PyVisitorBase<PyASTVisitor, ASTVisitor, VisitFlags::AllGood> {
    using PyVisitorBase::PyVisitorBase;
};

template<typename T>
void pyASTVisit(const T& t, py::object f = py::none(), py::object lookup_table = py::none()) {
    if (f.is_none() && lookup_table.is_none())
        throw py::type_error("visit() requires 'f' or 'lookup_table' (both are None)");
    std::optional<py::dict> lt;
    if (!lookup_table.is_none())
        lt = py::cast<py::dict>(lookup_table);
    PyASTVisitor visitor{f, std::move(lt)};
    t.visit(visitor);
}
