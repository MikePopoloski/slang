//------------------------------------------------------------------------------
//! @file Matchers.h
//! @brief AST Matchers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once
#include <type_traits>

namespace slang::ast::matchers::internal {
namespace detail {

template<typename T>
struct MemberFunctionArgumentHelper;

// For non-const member functions
template<typename R, typename C, typename Arg0, typename... Args>
struct MemberFunctionArgumentHelper<R (C::*)(Arg0, Args...)> {
    using FirstArgType = Arg0;
};

// For const member functions
template<typename R, typename C, typename Arg0, typename... Args>
struct MemberFunctionArgumentHelper<R (C::*)(Arg0, Args...) const> {
    using FirstArgType = Arg0;
};

} // namespace detail

template<typename MatcherImp>
struct ExtractNodeType {
    using DeducedArgType =
        typename detail::MemberFunctionArgumentHelper<decltype(&MatcherImp::matches)>::FirstArgType;
    using type = std::remove_cv_t<std::remove_reference_t<DeducedArgType>>;
};
} // namespace slang::ast::matchers::internal
