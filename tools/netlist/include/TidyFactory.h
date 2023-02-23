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

class TidyCheck;

class Registry {
public:
    struct RegistryCheckConfig {
        std::string clkName;
        std::string resetName;
        bool resetIsActiveHigh;
    };

    using RegistryFunction = std::function<std::unique_ptr<TidyCheck>(const RegistryCheckConfig&)>;
    struct RegistryValue {
        slang::TidyKind kind;
        RegistryFunction creator;
    };
    using RegistryKey = std::string;
    using RegistryItem = std::pair<RegistryKey, RegistryValue>;
    using RegistryMap = std::unordered_map<RegistryKey, RegistryValue>;

    static bool add(const std::string& name, const slang::TidyKind& kind,
                    const RegistryFunction& func) {
        items()[name] = {kind, func};
        return true;
    }

    static std::unique_ptr<TidyCheck> create(const std::string& name) {
        if (items().find(name) == items().end())
            throw std::runtime_error(name + " has not been registered");
        return items()[name].creator(config());
    }

    static std::vector<std::string> get_registered() {
        std::vector<std::string> ret;
        for (const auto& item : items())
            ret.push_back(item.first);
        return ret;
    }

    template<typename F>
    static std::vector<std::string> get_registered(F&& function) {
        std::vector<std::string> ret;
        for (const auto& item : items())
            if (function(item))
                ret.push_back(item.first);
        return ret;
    }

    static void initialize_default_check_config() {
        config().clkName = "clk_i";
        config().resetName = "rst_ni";
        config().resetIsActiveHigh = true;
    }

    static void set_check_config_clock_name(const std::string_view& name) {
        config().clkName = name;
    }
    static void set_check_config_reset_name(const std::string_view& name) {
        config().resetName = name;
    }
    static void set_check_config_reset_active_high(bool activeHigh) {
        config().resetIsActiveHigh = activeHigh;
    }

private:
    static RegistryMap& items() {
        static RegistryMap map;
        return map;
    }

    static RegistryCheckConfig& config() {
        static RegistryCheckConfig config;
        return config;
    }
};

class TidyCheck {
public:
    explicit TidyCheck(const Registry::RegistryCheckConfig& config, slang::TidyKind kind) :
        config(config), kind(kind) {}
    virtual ~TidyCheck() = default;

    [[nodiscard]] virtual bool check(const slang::ast::RootSymbol& root) = 0;

    virtual std::string_view name() const = 0;
    virtual std::string description() const = 0;
    virtual std::string_view shortDescription() const = 0;

    virtual slang::DiagCode diagCode() const = 0;
    virtual slang::DiagnosticSeverity diagSeverity() const = 0;
    virtual std::string diagString() const = 0;

    [[nodiscard]] virtual const slang::Diagnostics& getDiagnostics() const { return diagnostics; }
    [[nodiscard]] virtual const slang::TidyKind getKind() const { return kind; }

protected:
    slang::Diagnostics diagnostics;
    slang::TidyKind kind;
    const Registry::RegistryCheckConfig& config;
};

#define REGISTER(name, class_name, kind)                                           \
    static auto name##_entry = Registry::add(#name, kind, [](const auto& config) { \
        return std::make_unique<class_name>(config, kind);                         \
    });
