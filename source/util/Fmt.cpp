//------------------------------------------------------------------------------
// Fmt.cpp
// Single translation unit that compiles the fmt library implementation
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

// slang consumes fmt as a header-only library, but we don't want the fmt
// implementation compiled into every TU that includes a fmt header. The
// FMT_HEADER_ONLY define is therefore stripped from the fmt target (see
// external/CMakeLists.txt) and the implementation is compiled here, in exactly
// one TU. Including format-inl.h directly (rather than defining
// FMT_HEADER_ONLY) leaves FMT_FUNC empty so the symbols have external linkage
// and can be referenced from the rest of the library.
#include <fmt/format-inl.h>

FMT_BEGIN_NAMESPACE

#if FMT_USE_LOCALE
template FMT_API locale_ref::locale_ref(const std::locale& loc);
template FMT_API auto locale_ref::get<std::locale>() const -> std::locale;
#endif

namespace detail {

template FMT_API auto dragonbox::to_decimal(float x) noexcept -> dragonbox::decimal_fp<float>;
template FMT_API auto dragonbox::to_decimal(double x) noexcept -> dragonbox::decimal_fp<double>;

// Explicit instantiations for char.
template FMT_API auto thousands_sep_impl(locale_ref) -> thousands_sep_result<char>;
template FMT_API auto decimal_point_impl(locale_ref) -> char;

// Explicit instantiations for wchar_t.
template FMT_API auto thousands_sep_impl(locale_ref) -> thousands_sep_result<wchar_t>;
template FMT_API auto decimal_point_impl(locale_ref) -> wchar_t;

} // namespace detail

FMT_END_NAMESPACE
