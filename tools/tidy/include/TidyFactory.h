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

class TidyCheck {
public:
    virtual ~TidyCheck() = default;

    [[nodiscard]] virtual bool check(const slang::ast::RootSymbol& root) = 0;
    virtual std::string_view name() const = 0;

    [[nodiscard]] virtual const slang::Diagnostics& getDiagnostics() const { return diagnostics; }

protected:
    slang::Diagnostics diagnostics;
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
            throw std::runtime_error(name + "has not been registered");
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

#define REGISTER(name, class_name) \
    static auto name##_entry = Registry::add(#name, [] { return std::make_unique<class_name>(); });
