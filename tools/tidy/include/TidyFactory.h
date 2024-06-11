//------------------------------------------------------------------------------
//! @file TidyFactory.h
//! @brief Factory object for slang-tidy
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "TidyConfig.h"
#include "TidyKind.h"
#include <functional>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/text/SourceManager.h"
#include "slang/util/Util.h"

class TidyCheck;

class Registry {
public:
    using RegistryFunction = std::function<std::unique_ptr<TidyCheck>()>;
    struct RegistryValue {
        slang::TidyKind kind;
        RegistryFunction creator;
    };
    using RegistryKey = std::string;
    using RegistryMap = std::unordered_map<RegistryKey, RegistryValue>;

    Registry() = default;

    // Prevent copies from being made.
    Registry(Registry const&) = delete;
    void operator=(Registry const&) = delete;

    static bool add(const std::string& name, const slang::TidyKind& kind,
                    const RegistryFunction& func) {
        checks()[name] = {kind, func};
        return true;
    }

    static std::unique_ptr<TidyCheck> create(const std::string& name) {
        if (checks().find(name) == checks().end())
            SLANG_THROW(std::runtime_error(name + " has not been registered"));
        return checks()[name].creator();
    }

    static std::vector<std::string> getRegisteredChecks() {
        std::vector<std::string> ret;
        for (const auto& check : checks())
            ret.push_back(check.first);
        return ret;
    }

    static std::vector<std::string> getEnabledChecks() {
        std::vector<std::string> ret;
        for (const auto& check : checks())
            if (config().isCheckEnabled(check.second.kind, check.first))
                ret.push_back(check.first);
        return ret;
    }

    static void setConfig(TidyConfig& newConfig) { config() = newConfig; }

    static const TidyConfig& getConfig() { return config(); }

    static void setSourceManager(const slang::SourceManager* sm) { *sourceManager() = sm; }
    static slang::not_null<const slang::SourceManager*> getSourceManager() {
        if (auto sm = *sourceManager(); sm == nullptr)
            SLANG_THROW(std::runtime_error("TidyFactory: Trying to get SourceManager, but factory "
                                           "pointer has not been initialized"));
        return slang::not_null<const slang::SourceManager*>(*sourceManager());
    }

private:
    static RegistryMap& checks() {
        static RegistryMap map;
        return map;
    }

    static TidyConfig& config() {
        static TidyConfig config;
        return config;
    }

    static const slang::SourceManager** sourceManager() {
        static const slang::SourceManager* sm;
        return &sm;
    }
};

class TidyCheck {
public:
    explicit TidyCheck(slang::TidyKind kind) : kind(kind) {}
    virtual ~TidyCheck() = default;

    /// Returns true if the check didn't find any errors, false otherwise
    [[nodiscard]] virtual bool check(const slang::ast::RootSymbol& root) = 0;

    virtual std::string name() const = 0;
    virtual std::string description() const = 0;
    virtual std::string shortDescription() const = 0;

    virtual slang::DiagCode diagCode() const = 0;
    virtual slang::DiagnosticSeverity diagSeverity() const = 0;
    virtual std::string diagString() const = 0;

    std::string diagMessage() const {
        auto kindStr = std::string(toString(kind));
        std::transform(kindStr.begin(), kindStr.end(), kindStr.begin(), ::toupper);
        return fmt::format("[{}-{}] {}", kindStr, diagCode().getCode(), diagString());
    }

    [[nodiscard]] virtual const slang::Diagnostics& getDiagnostics() const { return diagnostics; }
    [[nodiscard]] virtual const slang::TidyKind getKind() const { return kind; }

protected:
    slang::Diagnostics diagnostics;
    slang::TidyKind kind;
};

#define REGISTER(name, class_name, kind)                  \
    static auto name##_entry = Registry::add(#name, kind, \
                                             []() { return std::make_unique<class_name>(kind); });
