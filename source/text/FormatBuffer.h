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

#include "slang/util/TextStyle.h"

namespace slang::detail {

inline fmt::terminal_color toFmtTerminalColor(TerminalColor color) {
    switch (color) {
        case TerminalColor::Black:
            return fmt::terminal_color::black;
        case TerminalColor::Red:
            return fmt::terminal_color::red;
        case TerminalColor::Green:
            return fmt::terminal_color::green;
        case TerminalColor::Yellow:
            return fmt::terminal_color::yellow;
        case TerminalColor::Blue:
            return fmt::terminal_color::blue;
        case TerminalColor::Magenta:
            return fmt::terminal_color::magenta;
        case TerminalColor::Cyan:
            return fmt::terminal_color::cyan;
        case TerminalColor::White:
            return fmt::terminal_color::white;
        case TerminalColor::BrightBlack:
            return fmt::terminal_color::bright_black;
        case TerminalColor::BrightRed:
            return fmt::terminal_color::bright_red;
        case TerminalColor::BrightGreen:
            return fmt::terminal_color::bright_green;
        case TerminalColor::BrightYellow:
            return fmt::terminal_color::bright_yellow;
        case TerminalColor::BrightBlue:
            return fmt::terminal_color::bright_blue;
        case TerminalColor::BrightMagenta:
            return fmt::terminal_color::bright_magenta;
        case TerminalColor::BrightCyan:
            return fmt::terminal_color::bright_cyan;
        case TerminalColor::BrightWhite:
            return fmt::terminal_color::bright_white;
    }
    return fmt::terminal_color::white;
}

inline fmt::text_style toFmtTextStyle(const TextStyle& style) {
    fmt::text_style result;
    if (style.hasForeground()) {
        auto color = style.foreground();
        if (color.isRgb())
            result |= fmt::fg(fmt::rgb(color.rgb()));
        else
            result |= fmt::fg(toFmtTerminalColor(color.terminal()));
    }

    if (style.hasBackground()) {
        auto color = style.background();
        if (color.isRgb())
            result |= fmt::bg(fmt::rgb(color.rgb()));
        else
            result |= fmt::bg(toFmtTerminalColor(color.terminal()));
    }

    if (style.emphasis())
        result |= static_cast<fmt::emphasis>(style.emphasis());

    return result;
}

} // namespace slang::detail

namespace slang {

class FormatBuffer {
public:
    void append(std::string_view str) { buf.append(str.data(), str.data() + str.size()); }
    void append(char ch) { buf.push_back(ch); }

    void append(const TextStyle& style, std::string_view str) { format(style, "{}", str); }

    template<typename... Args>
    void format(fmt::format_string<Args...> fmt, Args&&... args) {
        fmt::detail::vformat_to(buf, fmt.get(), fmt::make_format_args(args...));
    }

    template<typename... Args>
    void format(const TextStyle& style, fmt::format_string<Args...> fmt, Args&&... args) {
        if (!showColors) {
            fmt::detail::vformat_to(buf, fmt.get(), fmt::make_format_args(args...));
        }
        else {
            fmt::detail::vformat_to(buf, detail::toFmtTextStyle(style), fmt.get(),
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
