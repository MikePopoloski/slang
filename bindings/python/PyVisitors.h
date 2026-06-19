//------------------------------------------------------------------------------
// PyVisitors.h
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "pyslang.h"
#include <tuple>
#include <unordered_map>

#include "slang/ast/ASTVisitor.h"

enum class VisitAction {
    Advance,
    Skip,
    Interrupt,
};

// A compiled form of a Python `lookup_table` dict.
//
// A single lookup_table may mix keys from several different node-kind enum types
// (e.g. SymbolKind, ExpressionKind, ...). We keep one C++ hash map per enum type,
// so that during traversal the per-node membership test is a plain C++ lookup on
// the node's own `kind` enum and Python is only entered for matched nodes.
//
// The set of enum types is fixed at compile time by `Kinds...`. handle<T> dispatches
// on `decltype(t.kind)`, so if a visited node's kind type is not listed here it is a
// compile error rather than a silently dropped handler.
template<typename... Kinds>
struct KindHandlerTables {
    std::tuple<std::unordered_map<Kinds, py::object>...> maps;

    template<typename KindT>
    std::unordered_map<KindT, py::object>& mapFor() {
        return std::get<std::unordered_map<KindT, py::object>>(maps);
    }

    // Try to place one (key, value) pair into the map for KindT. Returns false if the
    // key is not an instance of that enum type, so callers can try the next type.
    template<typename KindT>
    bool tryInsert(py::handle key, py::handle value) {
        if (!py::isinstance<KindT>(key))
            return false;
        mapFor<KindT>().insert_or_assign(py::cast<KindT>(key),
                                         py::reinterpret_borrow<py::object>(value));
        return true;
    }

    // Compile the Python dict once into the typed maps.
    void build(const py::dict& table) {
        for (auto item : table)
            (tryInsert<Kinds>(item.first, item.second) || ...);
    }

    template<typename KindT>
    py::handle find(KindT kind) {
        auto& m = mapFor<KindT>();
        auto it = m.find(kind);
        return it == m.end() ? py::handle() : py::handle(it->second);
    }
};

template<typename Tuple>
struct KindTablesFor;

template<typename... Ks>
struct KindTablesFor<std::tuple<Ks...>> {
    using type = KindHandlerTables<Ks...>;
};

template<typename TDerived, typename KindList, template<class, auto...> class BaseVisitor,
         auto... baseArgs>
struct PyVisitorBase : public BaseVisitor<TDerived, baseArgs...> {
    py::object f;
    std::optional<py::dict> lookupTable;
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
        "traversed without invoking Python. `f` is not called in this mode.\n\n"
        "The `lookup_table` is compiled into native lookups when the visit begins and must "
        "not be mutated during traversal.";

    explicit PyVisitorBase(py::object f, std::optional<py::dict> lt = std::nullopt) :
        f{f}, lookupTable{std::move(lt)}, actionInterrupt{py::cast(VisitAction::Interrupt)},
        actionSkip{py::cast(VisitAction::Skip)} {
        if (this->lookupTable)
            tables.build(*this->lookupTable);
    }

    template<typename T>
    void handle(const T& t) {
        if (this->interrupted)
            return;

        py::object result;
        if (this->lookupTable) {
            if constexpr (requires { t.kind; }) {
                py::handle handler = tables.find(t.kind);
                if (handler)
                    result = handler(&t);
            }
        }
        else {
            result = this->f(&t);
        }

        if (this->applyResult(result))
            this->visitDefault(t);
    }

protected:
    // Returns true if the node's children should be visited. Handlers communicate intent by
    // returning a VisitAction (or None to advance). The VisitAction objects are cached so the
    // comparison does not re-cast them per node; value comparison (==) is kept to match the
    // previous behavior, and it only runs on a non-None return.
    bool applyResult(const py::object& result) {
        if (!result || result.is_none())
            return true;
        if (result.equal(actionInterrupt)) {
            this->interrupted = true;
            return false;
        }
        return result.not_equal(actionSkip);
    }

    typename KindTablesFor<KindList>::type tables;

private:
    py::object actionInterrupt;
    py::object actionSkip;
};

struct PyASTVisitor
    : PyVisitorBase<PyASTVisitor,
                    std::tuple<SymbolKind, ExpressionKind, StatementKind, TimingControlKind,
                               ConstraintKind, AssertionExprKind, BinsSelectExprKind, PatternKind>,
                    ASTVisitor, VisitFlags::AllGood> {
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
