//------------------------------------------------------------------------------
// pyslang.h
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <fmt/format.h>
#include <iterator>
#include <nanobind/make_iterator.h>
#include <nanobind/nanobind.h>
#include <nanobind/operators.h>
#include <nanobind/stl/detail/nb_dict.h>
#include <nanobind/stl/detail/nb_list.h>
#include <nanobind/stl/detail/nb_set.h>
#include <nanobind/stl/filesystem.h>
#include <nanobind/stl/function.h>
#include <nanobind/stl/optional.h>
#include <nanobind/stl/pair.h>
#include <nanobind/stl/shared_ptr.h>
#include <nanobind/stl/string.h>
#include <nanobind/stl/string_view.h>
#include <nanobind/stl/unique_ptr.h>
#include <nanobind/stl/variant.h>
#include <nanobind/stl/vector.h>
#include <nanobind/trampoline.h>
#include <optional>
#include <span>
#include <tuple>
#include <type_traits>
#include <vector>

#include "slang/ast/ASTVisitor.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/Enum.h"
#include "slang/util/Hash.h"
#include "slang/util/ScopeGuard.h"

#define STRINGIFY(x) #x
#define MACRO_STRINGIFY(x) STRINGIFY(x)

namespace nb = nanobind;
using namespace nanobind::literals;

using namespace slang;
using namespace slang::parsing;
using namespace slang::syntax;
using namespace slang::ast;

#define EXPOSE_ENUM(handle, name)                                \
    do {                                                         \
        nb::enum_<name> e(handle, #name);                        \
        for (auto member : name##_traits::values) {              \
            std::string nameStr = std::string(toString(member)); \
            if (nameStr == "None")                               \
                nameStr = "None_";                               \
            if (nameStr == "and")                                \
                nameStr = "and_";                                \
            if (nameStr == "or")                                 \
                nameStr = "or_";                                 \
            e.value(nameStr.c_str(), member);                    \
        }                                                        \
    } while (0)

// nanobind's return-value policies. Unlike pybind11, nanobind returns raw
// pointers/references as non-owning by default, which is exactly what slang's
// arena-allocated nodes require. These short aliases keep call sites terse.
static constexpr auto byref = nb::rv_policy::reference;
static constexpr auto byrefint = nb::rv_policy::reference_internal;

// ---------------------------------------------------------------------------
// Multiple-inheritance shims.
//
// slang's IR mixes in slang::ast::Scope and slang::ast::ParameterSymbolBase
// as additional base classes of many Symbol/Type subclasses. nanobind, unlike
// pybind11, supports only a single base class per nb::class_ (plus an optional
// trampoline alias), so we register these classes with just their primary
// Symbol/Type base and re-expose the secondary base's Python API on each
// subclass via the helpers below. The bindings mirror the standalone Scope /
// ParameterSymbolBase class bindings exactly (same names, signatures and
// return-value policies), differing only in that the lambdas take the concrete
// Derived type and call through the (public) secondary base. `decltype(auto)`
// return types preserve the reference/pointer/value category of each accessor
// so that nanobind resolves the identical (method-default, non-owning)
// rv_policy as the original member-pointer bindings.
//
// NOTE: a behavioral consequence is that `isinstance(x, Scope)` /
// `isinstance(x, ParameterSymbolBase)` is False for these subclasses in Python,
// since they no longer inherit the base type but only its methods.
template<typename Derived, typename... Extra>
void addScopeMethods(nb::class_<Derived, Extra...>& cls) {
    cls.def_prop_ro("compilation",
                    [](const Derived& self) -> decltype(auto) {
                        return self.Scope::getCompilation();
                    })
        .def_prop_ro("defaultNetType",
                     [](const Derived& self) -> decltype(auto) {
                         return self.Scope::getDefaultNetType();
                     })
        .def_prop_ro("timeScale",
                     [](const Derived& self) -> decltype(auto) {
                         return self.Scope::getTimeScale();
                     })
        .def_prop_ro("isProceduralContext",
                     [](const Derived& self) -> decltype(auto) {
                         return self.Scope::isProceduralContext();
                     })
        .def_prop_ro("containingInstance",
                     [](const Derived& self) -> decltype(auto) {
                         return self.Scope::getContainingInstance();
                     })
        .def_prop_ro("compilationUnit",
                     [](const Derived& self) -> decltype(auto) {
                         return self.Scope::getCompilationUnit();
                     })
        .def_prop_ro("isUninstantiated",
                     [](const Derived& self) -> decltype(auto) {
                         return self.Scope::isUninstantiated();
                     })
        .def(
            "find", [](const Derived& self, std::string_view arg) { return self.Scope::find(arg); },
            byrefint)
        .def(
            "lookupName",
            [](const Derived& self, std::string_view arg, LookupLocation location,
               bitmask<LookupFlags> flags) { return self.Scope::lookupName(arg, location, flags); },
            "name"_a, "location"_a = LookupLocation::max, "flags"_a = LookupFlags::None, byrefint)
        .def("__getitem__",
             [](const Derived& self, size_t idx) {
                 auto members = self.Scope::members();
                 members.advance(ptrdiff_t(idx));
                 if (members.begin() == members.end())
                     throw nb::index_error();

                 return nb::cast(&members.front(), byrefint, nb::cast(&self));
             })
        .def("__len__",
             [](const Derived& self) {
                 auto members = self.Scope::members();
                 return std::distance(members.begin(), members.end());
             })
        .def(
            "__iter__",
            [](const Derived& self) {
                auto members = self.Scope::members();
                // Scope::members() dereferences to `const Symbol&`; nanobind's
                // default automatic_reference policy would try to *copy* that
                // (non-copyable) symbol and abort. Force non-owning references
                // (the symbols live in the compilation arena).
                return nb::make_iterator<nb::rv_policy::reference>(nb::type<Derived>(),
                                                                   "ScopeIterator", members.begin(),
                                                                   members.end());
            },
            nb::keep_alive<0, 1>());
}

// Registers a Symbol/Type subclass that also inherits slang::ast::Scope,
// re-exposing the Scope API. Returns the class_ so the caller can chain its own
// members, e.g. `scopeClass<Foo, Symbol>(m, "Foo").def(...);`
template<typename Derived, typename Base>
nb::class_<Derived, Base> scopeClass(nb::handle scope, const char* name) {
    nb::class_<Derived, Base> cls(scope, name);
    addScopeMethods(cls);
    return cls;
}

// Re-exposes slang::ast::ParameterSymbolBase's Python API on a subclass.
template<typename Derived, typename... Extra>
void addParameterBaseMethods(nb::class_<Derived, Extra...>& cls) {
    cls.def_prop_ro("isLocalParam",
                    [](const Derived& self) -> decltype(auto) {
                        return self.ParameterSymbolBase::isLocalParam();
                    })
        .def_prop_ro("isPortParam",
                     [](const Derived& self) -> decltype(auto) {
                         return self.ParameterSymbolBase::isPortParam();
                     })
        .def_prop_ro("isBodyParam", [](const Derived& self) -> decltype(auto) {
            return self.ParameterSymbolBase::isBodyParam();
        });
}

// Registers a Symbol subclass that also (C++-)inherits ParameterSymbolBase,
// re-exposing its API. Returns the class_ so the caller can chain its members.
template<typename Derived, typename Base>
nb::class_<Derived, Base> paramClass(nb::handle scope, const char* name) {
    nb::class_<Derived, Base> cls(scope, name);
    addParameterBaseMethods(cls);
    return cls;
}

namespace nanobind {
namespace detail {

// Returns the PEP 3118 buffer format character for an arithmetic type. This
// mirrors pybind11's format_descriptor<T>::c mapping (which is size/signedness
// based, so e.g. `long` maps to the same code as `int64_t`).
template<typename T>
constexpr char buffer_format_char() {
    using U = std::remove_cv_t<T>;
    if constexpr (std::is_same_v<U, bool>) {
        return '?';
    }
    else if constexpr (std::is_floating_point_v<U>) {
        if constexpr (sizeof(U) == 4)
            return 'f';
        else if constexpr (sizeof(U) == 8)
            return 'd';
        else
            return 'g';
    }
    else if constexpr (std::is_integral_v<U>) {
        constexpr bool s = std::is_signed_v<U>;
        if constexpr (sizeof(U) == 1)
            return s ? 'b' : 'B';
        else if constexpr (sizeof(U) == 2)
            return s ? 'h' : 'H';
        else if constexpr (sizeof(U) == 4)
            return s ? 'i' : 'I';
        else if constexpr (sizeof(U) == 8)
            return s ? 'q' : 'Q';
        else
            return '\0';
    }
    else {
        return '\0';
    }
}

// Returns {true, a span referencing the data contained by src} without copying
// or converting the data if possible. Otherwise returns {false, an empty span}.
template<typename T>
    requires std::is_arithmetic_v<T>
std::tuple<bool, std::span<T>> loadSpanFromBuffer(handle src) {
    Py_buffer view;
    int flags = PyBUF_STRIDES | PyBUF_FORMAT;
    if (!std::is_const<T>::value)
        flags |= PyBUF_WRITABLE;
    if (PyObject_GetBuffer(src.ptr(), &view, flags) == 0) {
        auto cleanup = ScopeGuard([&view] { PyBuffer_Release(&view); });
        if (view.ndim == 1 && view.strides[0] == sizeof(T) && view.format &&
            view.format[0] == buffer_format_char<std::remove_cv_t<T>>()) {
            return {true, std::span<T>(static_cast<T*>(view.buf), view.shape[0])};
        }
    }
    else {
        // Clear the buffer error (failure is reported in the return value).
        PyErr_Clear();
    }
    return {false, std::span<T>()};
}
// If T is not a numeric type, the buffer interface cannot be used.
template<typename T>
    requires(!std::is_arithmetic_v<T>)
constexpr std::tuple<bool, std::span<T>> loadSpanFromBuffer(handle) {
    return {false, std::span<T>()};
}

template<typename T>
struct is_span : std::false_type {};
template<typename T>
struct is_span<std::span<T>> : std::true_type {};

// Convert between std::span and a Python buffer or sequence.
template<typename T>
struct type_caster<std::span<T>> {
    using value_type = std::remove_cv_t<T>;
    static_assert(!is_span<value_type>::value, "Nested spans are not supported.");

    using ListCaster = list_caster<std::vector<value_type>, value_type>;

    static constexpr auto Name = const_name("span[") + make_caster<T>::Name + const_name("]");

    // A span is a lightweight value (pointer + size) that points into storage
    // owned either by the source Python buffer or by `listCaster` below. It
    // remains valid for the duration of the enclosing function call, so it is
    // safe to hand out by value.
    template<typename T_>
    using Cast = std::span<T>;
    template<typename T_>
    static constexpr bool can_cast() {
        return true;
    }

    bool from_python(handle src, uint8_t flags, cleanup_list* cleanup) noexcept {
        // Attempt to reference a buffer, including np.ndarray and array.arrays.
        bool loaded;
        std::tie(loaded, value) = loadSpanFromBuffer<T>(src);
        if (loaded)
            return true;

        // Attempt to convert a native sequence. Only allowed for spans over
        // const elements, since the backing std::vector is owned by this caster
        // (a non-const span would let the caller mutate soon-to-be-freed data).
        if constexpr (std::is_const_v<T>) {
            if (listCaster.from_python(src, flags, cleanup)) {
                std::vector<value_type>& v = listCaster.value;
                value = std::span<T>(v.data(), v.size());
                return true;
            }
        }

        return false; // Python type cannot be loaded into a span.
    }

    template<typename CType>
    static handle from_cpp(CType&& src, rv_policy policy, cleanup_list* cleanup) noexcept {
        return ListCaster::from_cpp(std::forward<CType>(src), policy, cleanup);
    }

    explicit operator std::span<T>() { return value; }

private:
    ListCaster listCaster;
    std::span<T> value;
};

// Convert between flat_hash_map and python dict.
template<typename Key, typename Value, typename Hash, typename Equal, typename Alloc>
struct type_caster<flat_hash_map<Key, Value, Hash, Equal, Alloc>>
    : dict_caster<flat_hash_map<Key, Value, Hash, Equal, Alloc>, Key, Value> {};

// Convert between flat_hash_set and python set.
template<typename Key, typename Hash, typename Equal, typename Alloc>
struct type_caster<flat_hash_set<Key, Hash, Equal, Alloc>>
    : set_caster<flat_hash_set<Key, Hash, Equal, Alloc>, Key> {};

template<typename Type>
struct type_caster<not_null<Type>> {
    using Caster = make_caster<Type>;

    static constexpr auto Name = Caster::Name;
    template<typename T_>
    using Cast = not_null<Type>;
    template<typename T_>
    static constexpr bool can_cast() {
        return true;
    }

    bool from_python(handle src, uint8_t flags, cleanup_list* cleanup) noexcept {
        return caster.from_python(src, flags, cleanup);
    }

    static handle from_cpp(const not_null<Type>& src, rv_policy policy,
                           cleanup_list* cleanup) noexcept {
        return Caster::from_cpp(src.get(), policy, cleanup);
    }

    explicit operator not_null<Type>() { return not_null<Type>(caster.operator cast_t<Type>()); }

private:
    Caster caster;
};

template<typename Type>
struct type_caster<bitmask<Type>> {
    using Caster = make_caster<Type>;

    static constexpr auto Name = Caster::Name;
    template<typename T_>
    using Cast = bitmask<Type>;
    template<typename T_>
    static constexpr bool can_cast() {
        return true;
    }

    bool from_python(handle src, uint8_t flags, cleanup_list* cleanup) noexcept {
        return caster.from_python(src, flags, cleanup);
    }

    static handle from_cpp(const bitmask<Type>& src, rv_policy policy,
                           cleanup_list* cleanup) noexcept {
        Type tmp = static_cast<Type>(src.bits());
        return Caster::from_cpp(tmp, policy, cleanup);
    }

    explicit operator bitmask<Type>() { return bitmask<Type>(caster.operator cast_t<Type>()); }

private:
    Caster caster;
};

// Common base for SyntaxList<T>/SeparatedSyntaxList<T>/TokenList type casters.
// Derived must provide:
//   static constexpr auto Name = const_name("...");
//   static bool loadElement(handle item, std::vector<Element>& storage);
//   static void appendCast(list& result, const ListType& src);
template<typename Derived, typename ListType, typename Element>
struct syntax_list_caster_base {
    using Value = ListType;
    template<typename T_>
    using Cast = movable_cast_t<T_>;
    template<typename T_>
    static constexpr bool can_cast() {
        return true;
    }

    bool from_python(handle src, uint8_t, cleanup_list*) noexcept {
        if (!PySequence_Check(src.ptr()))
            return false;

        Py_ssize_t n = PySequence_Size(src.ptr());
        if (n < 0) {
            PyErr_Clear();
            return false;
        }

        std::vector<Element> vec;
        vec.reserve(static_cast<size_t>(n));
        for (Py_ssize_t i = 0; i < n; ++i) {
            object item = steal(PySequence_GetItem(src.ptr(), i));
            if (!item.is_valid()) {
                PyErr_Clear();
                return false;
            }
            if (!Derived::loadElement(item, vec))
                return false;
        }

        value = ListType(alloc, vec);
        return true;
    }

    static handle from_cpp(const ListType& src, rv_policy, cleanup_list*) noexcept {
        list result;
        Derived::appendCast(result, src);
        return result.release();
    }

    static handle from_cpp(const ListType* src, rv_policy policy, cleanup_list* cleanup) noexcept {
        if (!src)
            return none().release();
        return from_cpp(*src, policy, cleanup);
    }

    explicit operator ListType*() { return &value; }
    explicit operator ListType&() { return value; }
    explicit operator ListType&&() { return static_cast<ListType&&>(value); }

protected:
    // BumpAllocator that backs the wrapped list's storage. Owned by this caster
    // so that the wrapped list remains valid for the duration of the binding
    // call.
    slang::BumpAllocator alloc;
    ListType value{};
};

template<typename T>
struct type_caster<SyntaxList<T>>
    : syntax_list_caster_base<type_caster<SyntaxList<T>>, SyntaxList<T>, T*> {
    static constexpr auto Name = const_name("SyntaxList");

    static bool loadElement(handle item, std::vector<T*>& storage) {
        T* out = nullptr;
        if (!try_cast<T*>(item, out))
            return false;
        storage.push_back(out);
        return true;
    }

    static void appendCast(list& result, const SyntaxList<T>& src) {
        for (T* item : src) {
            result.append(
                steal(type_caster<SyntaxNode>::from_cpp(item, rv_policy::reference, nullptr)));
        }
    }
};

template<typename T>
struct type_caster<SeparatedSyntaxList<T>>
    : syntax_list_caster_base<type_caster<SeparatedSyntaxList<T>>, SeparatedSyntaxList<T>,
                              TokenOrSyntax> {
    static constexpr auto Name = const_name("SeparatedSyntaxList");

    static bool loadElement(handle item, std::vector<TokenOrSyntax>& storage) {
        if (isinstance<Token>(item)) {
            Token tok;
            if (!try_cast<Token>(item, tok))
                return false;
            storage.push_back(tok);
            return true;
        }

        T* out = nullptr;
        if (!try_cast<T*>(item, out))
            return false;
        storage.push_back(out);
        return true;
    }

    static void appendCast(list& result, const SeparatedSyntaxList<T>& src) {
        for (size_t i = 0, count = src.getChildCount(); i < count; ++i) {
            auto ele = src.getChild(i);
            if (ele.isToken()) {
                result.append(
                    steal(type_caster<Token>::from_cpp(ele.token(), rv_policy::copy, nullptr)));
            }
            else if (ele.node()) {
                result.append(steal(
                    type_caster<SyntaxNode>::from_cpp(ele.node(), rv_policy::reference, nullptr)));
            }
        }
    }
};

template<>
struct type_caster<TokenList> : syntax_list_caster_base<type_caster<TokenList>, TokenList, Token> {
    static constexpr auto Name = const_name("TokenList");

    static bool loadElement(handle item, std::vector<Token>& storage) {
        if (!isinstance<Token>(item))
            return false;
        Token tok;
        if (!try_cast<Token>(item, tok))
            return false;
        storage.push_back(tok);
        return true;
    }

    static void appendCast(list& result, const TokenList& src) {
        for (auto t : src) {
            result.append(steal(type_caster<Token>::from_cpp(t, rv_policy::copy, nullptr)));
        }
    }
};

// Helper for the polymorphic type hooks below. Unlike pybind11's
// polymorphic_type_hook, nanobind's type_hook does NOT fall back to a
// registered base class when the concrete type_info it returns is not
// registered: nb_type_put simply fails the conversion. To preserve graceful
// degradation, where only base classes are bound), only return the concrete
// type when it is actually registered; otherwise return the statically-known
// base so the conversion still succeeds.
inline const std::type_info* registeredOr(const std::type_info* concrete,
                                          const std::type_info* fallback) noexcept {
    if (concrete && nb_type_lookup(concrete))
        return concrete;
    return fallback;
}

// Downcast SyntaxNode -> concrete syntax type using its runtime `kind`.
template<typename T>
struct type_hook<T, std::enable_if_t<std::is_base_of_v<SyntaxNode, T>, int>> {
    static const std::type_info* get(const T* src) {
        if (!src)
            return &typeid(T);
        return registeredOr(typeFromSyntaxKind(src->kind), &typeid(SyntaxNode));
    }
};

template<typename T>
using CanDowncast =
    std::enable_if_t<std::is_base_of_v<Symbol, T> || std::is_base_of_v<Statement, T> ||
                         std::is_base_of_v<Expression, T> || std::is_base_of_v<TimingControl, T> ||
                         std::is_base_of_v<Constraint, T> || std::is_base_of_v<AssertionExpr, T> ||
                         std::is_base_of_v<BinsSelectExpr, T> || std::is_base_of_v<Pattern, T>,
                     int>;

// Downcast Symbol/Statement/Expression/etc. via the slang visitor mechanism.
template<typename T>
struct type_hook<T, CanDowncast<T>> {
    struct DowncastVisitor {
        template<typename U>
        const std::type_info* visit(const U&) {
            return &typeid(U);
        }
    };

    static const std::type_info* get(const T* src) {
        if (!src)
            return &typeid(T);
        DowncastVisitor visitor;
        return registeredOr(src->visit(visitor), &typeid(T));
    }
};

template<>
struct type_hook<RandSeqProductionSymbol::ProdBase> {
    static const std::type_info* get(const RandSeqProductionSymbol::ProdBase* src) {
        if (!src)
            return &typeid(RandSeqProductionSymbol::ProdBase);

        const std::type_info* type = &typeid(RandSeqProductionSymbol::ProdBase);
        switch (src->kind) {
#define CASE(x, y)                                  \
    case RandSeqProductionSymbol::ProdKind::x:      \
        type = &typeid(RandSeqProductionSymbol::y); \
        break

            CASE(Item, ProdItem);
            CASE(CodeBlock, CodeBlockProd);
            CASE(IfElse, IfElseProd);
            CASE(Repeat, RepeatProd);
            CASE(Case, CaseProd);
#undef CASE
        }

        // ProdItem/CodeBlockProd/... derive from ProdBase as their first (and
        // only) base, so no pointer adjustment is required.
        return registeredOr(type, &typeid(RandSeqProductionSymbol::ProdBase));
    }
};

// NOTE: pybind11's hook downcast ParameterSymbolBase by offsetting to its
// embedded `symbol` member (a Symbol subobject at a nonzero offset) and running
// the Symbol hook. nanobind's type_hook cannot express a pointer adjustment --
// it only returns a type_info while nb_type_put uses the original pointer -- so
// we cannot reproduce that offsetting here, and this hook only reports the base
// type. The one binding that surfaces ParameterSymbolBase pointers to Python
// (InstanceBodySymbol.parameters) instead returns each parameter's embedded
// `symbol` subobject, which the Symbol hook downcasts to the concrete
// ParameterSymbol / TypeParameterSymbol (see SymbolBindings.cpp). This hook thus
// remains as a safe fallback for any other ParameterSymbolBase pointer.
template<>
struct type_hook<ParameterSymbolBase> {
    static const std::type_info* get(const ParameterSymbolBase*) {
        return &typeid(ParameterSymbolBase);
    }
};

} // namespace detail
} // namespace nanobind
