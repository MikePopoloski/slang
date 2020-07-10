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

class FormatBuffer : public fmt::memory_buffer {
public:
    void append(std::string_view str) {
        fmt::memory_buffer::append(str.data(), str.data() + str.size());
    }

    void append(const fmt::text_style& style, std::string_view str) { format(style, "{}", str); }

    template<typename String, typename... Args>
    void format(const String& format, Args&&... args) {
        fmt::format_to(*static_cast<fmt::memory_buffer*>(this), format,
                       std::forward<Args>(args)...);
    }

    template<typename String, typename... Args>
    void format(const fmt::text_style& style, const String& format, Args&&... args) {
        if (!showColors) {
            fmt::format_to(*static_cast<fmt::memory_buffer*>(this), format,
                           std::forward<Args>(args)...);
        }
        else {
            fmt::detail::vformat_to(*static_cast<fmt::memory_buffer*>(this), style,
                                    fmt::to_string_view(format),
                                    { fmt::detail::make_args_checked<Args...>(format, args...) });
        }
    }

    char back() const { return data()[size() - 1]; }

    void pop_back() { resize(size() - 1); }

    void setColorsEnabled(bool enabled) { showColors = enabled; }

    std::string str() const {
        return fmt::to_string(*static_cast<const fmt::memory_buffer*>(this));
    }

private:
    bool showColors = false;
};

} // namespace slang