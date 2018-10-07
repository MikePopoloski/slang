//------------------------------------------------------------------------------
// FormatBuffer.h
// String formatting helper class.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <fmt/format.h>
#include <string_view>

namespace slang {

class FormatBuffer : public fmt::memory_buffer {
public:
    void append(std::string_view str) {
        fmt::memory_buffer::append(str.data(), str.data() + str.size());
    }

    template<typename String, typename... Args>
    void format(const String& format, Args&&... args) {
        fmt::format_to(*static_cast<fmt::memory_buffer*>(this), format,
                       std::forward<Args>(args)...);
    }

    void pop_back() { resize(size() - 1); }

    std::string str() const {
        return fmt::to_string(*static_cast<const fmt::memory_buffer*>(this));
    }
};

} // namespace slang