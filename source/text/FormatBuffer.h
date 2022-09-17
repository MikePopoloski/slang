//------------------------------------------------------------------------------
// FormatBuffer.h
// Internal string formatting helper class
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <fmt/color.h>
#include <string_view>

namespace slang {

class FormatBuffer {
public:
    void append(std::string_view str) { buf.append(str.data(), str.data() + str.size()); }

    void append(const fmt::text_style& style, std::string_view str) { format(style, "{}", str); }

    template<typename... Args>
    void format(fmt::format_string<Args...> fmt, Args&&... args) {
        fmt::detail::vformat_to(buf, fmt::string_view(fmt), fmt::make_format_args(args...));
    }

    template<typename... Args>
    void format(const fmt::text_style& style, fmt::format_string<Args...> fmt, Args&&... args) {
        if (!showColors) {
            fmt::detail::vformat_to(buf, fmt::string_view(fmt), fmt::make_format_args(args...));
        }
        else {
            fmt::detail::vformat_to(buf, style, fmt::string_view(fmt),
                                    fmt::make_format_args(args...));
        }
    }

    size_t size() const { return buf.size(); }
    const char* data() const { return buf.data(); }
    char back() const { return buf.data()[buf.size() - 1]; }
    bool empty() const { return buf.size() == 0; }

    void pop_back() { buf.resize(buf.size() - 1); }
    void clear() { buf.clear(); }
    void resize(size_t newSize) { buf.resize(newSize); }

    void setColorsEnabled(bool enabled) { showColors = enabled; }

    std::string str() const { return fmt::to_string(buf); }

private:
    fmt::memory_buffer buf;
    bool showColors = false;
};

} // namespace slang
