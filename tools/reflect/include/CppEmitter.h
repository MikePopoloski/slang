//------------------------------------------------------------------------------
//! @file CppEmitter.h
//! @brief C++ Emitter classes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include "fmt/format.h"
#include "fmt/ranges.h"
#include <filesystem>
#include <fstream>
#include <ranges>
#include <sstream>
#include <vector>

#include "slang/util/Util.h"

namespace fs = std::filesystem;

class HppFile {
public:
    explicit HppFile(const std::string_view name, const bool noSystemC) :
        fileName(std::string(name) + ".h") {
        includes.emplace_back("ostream");
        includes.emplace_back("cstddef");
        includes.emplace_back("cstdint");
        includes.emplace_back("string");
        includes.emplace_back("sstream");
        if (!noSystemC)
            includes.emplace_back("systemc.h");
    }

    void add(std::string&& code) { hpp << code; }
    void addInclude(std::string&& code) {
        if (std::ranges::find(includes, code) == includes.end())
            includes.emplace_back(code);
    }
    void addIncludeHeader(std::string_view code) {
        if (std::ranges::find(headers, code) == headers.end())
            headers.emplace_back(code);
    }
    void addWithIndent(std::string&& code) { hpp << indent(currentIndent) << code; }
    void increaseIndent() { currentIndent++; }
    void decreaseIndent() {
        SLANG_ASSERT(currentIndent != 0);
        currentIndent--;
    }

    std::string emit() const {
        auto includesTransform = std::views::transform(includes, [](const auto& inc) {
            return fmt::format("#include <{}>", inc);
        });
        auto headersTransform = std::views::transform(headers, [](const auto& h) {
            return fmt::format("#include \"{}.h\"", h);
        });
        return fmt::format("// {}\n#pragma once\n\n{}\n{}\n\n{}", fileName,
                           fmt::join(includesTransform, "\n"), fmt::join(headersTransform, "\n"),
                           hpp.str());
    }

    void emitToFile(const fs::path& path) const {
        auto outFile = std::ofstream(path / fileName);
        outFile << emit();
    }

private:
    std::stringstream hpp;
    std::vector<std::string> includes;
    std::vector<std::string_view> headers;
    std::string fileName;
    uint32_t currentIndent{0};

    static std::string indent(const uint64_t blocks) {
        std::string ret;
        for (auto i = 0; i < blocks * 4; i++)
            ret += " ";
        return ret;
    }
};

class CppEmitter {
public:
    explicit CppEmitter(const bool noSystemC) : noSystemC(noSystemC) {}

    [[nodiscard]] HppFile& newNamespace(const std::string_view name) {
        hppFiles.push_back(HppFile(name, noSystemC));
        return hppFiles.back();
    }

    std::string emit() const {
        std::stringstream ret;
        for (auto& hpp : hppFiles)
            ret << hpp.emit();
        return std::move(ret.str());
    }

    void emitToFile(const fs::path& path) const {
        for (auto& hpp : hppFiles)
            hpp.emitToFile(path);
    }

private:
    bool noSystemC;
    std::vector<HppFile> hppFiles;
};
