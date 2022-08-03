//------------------------------------------------------------------------------
// pyslang.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <fmt/format.h>
#include <pybind11/cast.h>
#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "slang/syntax/SyntaxNode.h"
#include "slang/util/Enum.h"
#include "slang/util/Hash.h"
#include "slang/util/ScopeGuard.h"

#define STRINGIFY(x) #x
#define MACRO_STRINGIFY(x) STRINGIFY(x)

namespace py = pybind11;
using namespace pybind11::literals;
using namespace slang;

#define EXPOSE_ENUM(handle, name)                         \
    do {                                                  \
        py::enum_<name> e(handle, #name);                 \
        for (auto m : name##_traits::values) {            \
            e.value(std::string(toString(m)).c_str(), m); \
        }                                                 \
    } while (0)

static constexpr auto byref = py::return_value_policy::reference;
static constexpr auto byrefint = py::return_value_policy::reference_internal;

namespace pybind11 {
namespace detail {

// Returns {true, a span referencing the data contained by src} without copying
// or converting the data if possible. Otherwise returns {false, an empty span}.
template<typename T, typename std::enable_if<std::is_arithmetic<T>::value, bool>::type = true>
std::tuple<bool, span<T>> loadSpanFromBuffer(handle src) {
    Py_buffer view;
    int flags = PyBUF_STRIDES | PyBUF_FORMAT;
    if (!std::is_const<T>::value)
        flags |= PyBUF_WRITABLE;
    if (PyObject_GetBuffer(src.ptr(), &view, flags) == 0) {
        auto cleanup = ScopeGuard([&view] { PyBuffer_Release(&view); });
        if (view.ndim == 1 && view.strides[0] == sizeof(T) &&
            view.format[0] == format_descriptor<T>::c) {
            return { true, span(static_cast<T*>(view.buf), view.shape[0]) };
        }
    }
    else {
        // Clear the buffer error (failure is reported in the return value).
        PyErr_Clear();
    }
    return { false, span<T>() };
}
// If T is not a numeric type, the buffer interface cannot be used.
template<typename T, typename std::enable_if<!std::is_arithmetic<T>::value, bool>::type = true>
constexpr std::tuple<bool, span<T>> loadSpanFromBuffer(handle src) {
    return { false, span<T>() };
}

template<typename T>
struct is_span : std::false_type {};
template<typename T>
struct is_span<span<T>> : std::true_type {};

template<typename T>
struct type_caster<span<T>> {
public:
    using value_type = typename std::remove_cv<T>::type;
    static_assert(!is_span<value_type>::value, "Nested spans are not supported.");

    type_caster() = default;
    // Copy and Move operations must ensure the span points to the copied or
    // moved vector (if any), not the original one. Allows implicit conversions.
    template<typename U>
    type_caster(const type_caster<span<U>>& other) {
        *this = other;
    }
    template<typename U>
    type_caster(type_caster<span<U>>&& other) {
        *this = std::move(other);
    }
    template<typename U>
    type_caster& operator=(const type_caster<span<U>>& other) {
        list_caster = other.list_caster;
        value = list_caster ? get_value(*list_caster) : other.value;
        return *this;
    }
    template<typename U>
    type_caster& operator=(type_caster<span<U>>&& other) {
        list_caster = std::move(other.list_caster);
        value = list_caster ? get_value(*list_caster) : other.value;
        return *this;
    }

    static constexpr auto name = _("span[") + make_caster<T>::name + _("]");

    // We do not allow moving because 1) spans are super lightweight, so there's
    // no advantage to moving and 2) the span cannot exist without the caster,
    // so moving leaves an implicit dependency (while a reference or pointer
    // make that dependency explicit).
    operator span<T>*() { return &value; }
    operator span<T>&() { return value; }
    template<typename T_>
    using cast_op_type = cast_op_type<T_>;

    bool load(handle src, bool convert) {
        // Attempt to reference a buffer, including np.ndarray and array.arrays.
        bool loaded;
        std::tie(loaded, value) = loadSpanFromBuffer<T>(src);
        if (loaded)
            return true;

        // Attempt to unwrap an opaque std::vector.
        type_caster_base<std::vector<value_type>> caster;
        if (caster.load(src, false)) {
            value = get_value(caster);
            return true;
        }

        // Attempt to convert a native sequence. If the is_base_of_v check passes,
        // the elements do not require converting and pointers do not reference a
        // temporary object owned by the element caster. Pointers to converted
        // types are not allowed because they would result a dangling reference
        // when the element caster is destroyed.
        if (convert && std::is_const<T>::value &&
            (!std::is_pointer<T>::value ||
             std::is_base_of<type_caster_generic, make_caster<T>>::value)) {
            list_caster.emplace();
            if (list_caster->load(src, convert)) {
                value = get_value(*list_caster);
                return true;
            }
            else {
                list_caster.reset();
            }
        }

        return false; // Python type cannot be loaded into a span.
    }

    template<typename CType>
    static handle cast(CType&& src, return_value_policy policy, handle parent) {
        return ListCaster::cast(src, policy, parent);
    }

private:
    template<typename Caster>
    span<T> get_value(Caster& caster) {
        return static_cast<std::vector<value_type>&>(caster);
    }

    using ListCaster = list_caster<std::vector<value_type>, value_type>;
    std::optional<ListCaster> list_caster;
    span<T> value;
};

// Convert between flat_hash_map and python dict.
template<typename Key, typename Value, typename Hash, typename Equal, typename Alloc>
struct type_caster<flat_hash_map<Key, Value, Hash, Equal, Alloc>>
    : map_caster<flat_hash_map<Key, Value, Hash, Equal, Alloc>, Key, Value> {};

// Convert between flat_hash_set and python set.
template<typename Key, typename Hash, typename Equal, typename Alloc>
struct type_caster<flat_hash_set<Key, Hash, Equal, Alloc>>
    : set_caster<flat_hash_set<Key, Hash, Equal, Alloc>, Key> {};

template<typename type>
class type_caster<not_null<type>> {
private:
    using caster_t = make_caster<type>;
    caster_t subcaster;

public:
    bool load(handle src, bool convert) { return subcaster.load(src, convert); }
    static constexpr auto name = caster_t::name;
    static handle cast(const not_null<type>& src, return_value_policy policy, handle parent) {
        return caster_t::cast(src.get(), policy, parent);
    }
    template<typename T>
    using cast_op_type = not_null<type>;
    explicit operator not_null<type>() { return cast_op<type>(subcaster); }
};

} // namespace detail

template<typename T>
struct is_SyntaxList : std::false_type {};
template<typename T>
struct is_SyntaxList<SyntaxList<T>> : std::true_type {};

template<typename T>
struct is_SeparatedSyntaxList : std::false_type {};
template<typename T>
struct is_SeparatedSyntaxList<SeparatedSyntaxList<T>> : std::true_type {};

template<typename T>
struct polymorphic_type_hook<T, detail::enable_if_t<std::is_base_of<SyntaxNode, T>::value>> {
    static const void* get(const T* src, const std::type_info*& type) {
        type = src ? typeFromSyntaxKind(src->kind) : nullptr;
        if constexpr (is_SyntaxList<T>::value || is_SeparatedSyntaxList<T>::value ||
                      std::is_same_v<T, TokenList>) {
            return static_cast<const SyntaxNode*>(src);
        }
        else {
            return src;
        }
    }
};

} // namespace pybind11
