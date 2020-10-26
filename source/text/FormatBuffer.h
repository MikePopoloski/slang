//------------------------------------------------------------------------------
// FormatBuffer.h
// Internal string formatting helper class
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <fmt/color.h>
#include <fmt/format.h>
#include <string_view>

namespace slang {

class FormatBuffer {
public:
    void append(std::string_view str) { buf.append(str.data(), str.data() + str.size()); }

    void append(const fmt::text_style& style, std::string_view str) { format(style, "{}", str); }

    template<typename String, typename... Args>
    void format(const String& format, Args&&... args) {
        fmt::format_to(buf, format, std::forward<Args>(args)...);
    }

    template<typename String, typename... Args>
    void format(const fmt::text_style& style, const String& format, Args&&... args) {
        if (!showColors) {
            fmt::format_to(buf, format, std::forward<Args>(args)...);
        }
        else {
            fmt::format_to(fmt::detail::buffer_appender(buf), style, format,
                           std::forward<Args>(args)...);
        }
    }

    size_t size() const { return buf.size(); }
    const char* data() const { return buf.data(); }
    char back() const { return buf.data()[buf.size() - 1]; }

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
