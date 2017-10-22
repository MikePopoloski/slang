//------------------------------------------------------------------------------
// prelude.h
// File is included automatically in all source files.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <climits>
#include <iterator>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

using std::array;
using std::byte;
using std::initializer_list;
using std::int8_t;
using std::int16_t;
using std::int32_t;
using std::int64_t;
using std::intptr_t;
using std::nullptr_t;
using std::numeric_limits;
using std::optional;
using std::pair;
using std::ptrdiff_t;
using std::size_t;
using std::string;
using std::string_view;
using std::tuple;
using std::uint8_t;
using std::uint16_t;
using std::uint32_t;
using std::uint64_t;
using std::uintptr_t;
using std::vector;

using std::make_pair;
using std::make_tuple;
using std::make_optional;
using std::nullopt;

// Clang 5.0 and 6.0 fails to compile <variant> from libstdc++
#ifdef __clang__
#include "compat/variant.h"
using mpark::variant;
using mpark::monostate;
namespace std {
using mpark::get;
using mpark::get_if;
using mpark::visit;
}
#else
#include <variant>
using std::variant;
using std::monostate;
#endif

#include "gsl/gsl"

using gsl::span;
using gsl::make_span;

#include "ppk_assert/ppk_assert.h"

// Just delegate our assert handling to the 3rd part lib
#define ASSERT PPK_ASSERT
#define THROW_UNREACHABLE throw std::logic_error("Default case should be unreachable!")
