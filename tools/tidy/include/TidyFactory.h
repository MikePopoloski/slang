//------------------------------------------------------------------------------
//! @file TidyFactory.h
//! @brief Factory object for slang-tidy
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <functional>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/util/Util.h"

namespace slang {
// clang-format off
    #define KIND(x) \
        x(Synthesis)
    ENUM(TidyKind, KIND)
    #undef KIND
// clang-format on
} // namespace slang

class TidyCheck {
public:
    explicit TidyCheck(slang::TidyKind kind) : kind(kind) {}
    virtual ~TidyCheck() = default;

    [[nodiscard]] virtual bool check(const slang::ast::RootSymbol& root) = 0;

    virtual std::string_view name() const = 0;

    virtual slang::DiagCode diagCode() const = 0;
    virtual slang::DiagnosticSeverity diagSeverity() const = 0;
    virtual std::string diagString() const = 0;

    [[nodiscard]] virtual const slang::Diagnostics& getDiagnostics() const { return diagnostics; }
    [[nodiscard]] virtual const slang::TidyKind getKind() const { return kind; }

protected:
    slang::Diagnostics diagnostics;
    slang::TidyKind kind;
};

class Registry {
public:
    using RegistryFunction = std::function<std::unique_ptr<TidyCheck>()>;
    using RegistryMap = std::unordered_map<std::string, RegistryFunction>;

    static bool add(const std::string& name, const RegistryFunction& func) {
        items()[name] = func;
        return true;
    }

    static std::unique_ptr<TidyCheck> create(const std::string& name) {
        if (items().find(name) == items().end())
            throw std::runtime_error(name + " has not been registered");
        return items()[name]();
    }

    static std::vector<std::string> get_registered() {
        std::vector<std::string> ret;
        for (const auto& item : items())
            ret.push_back(item.first);
        return ret;
    }

private:
    static RegistryMap& items() {
        static RegistryMap map;
        return map;
    }
};

#define REGISTER(name, class_name, kind)            \
    static auto name##_entry = Registry::add(#name, \
                                             [] { return std::make_unique<class_name>(kind); });
