//------------------------------------------------------------------------------
//! @file Json.h
//! @brief Minimal JSON serialization support
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

class FormatBuffer;

class JsonWriter {
public:
    JsonWriter();
    ~JsonWriter();

    void setIndentSize(int size) { indentSize = size; }
    void setPrettyPrint(bool enabled) { pretty = enabled; }

    string_view view() const;

    void startObject();
    void endObject();

    void startArray();
    void endArray();

    void writeProperty(string_view name);
    void writeValue(string_view value);
    void writeValue(int64_t value);
    void writeValue(uint64_t value);
    void writeValue(bool value);

private:
    void endValue();
    size_t findLastComma() const;
    void writeQuoted(string_view str);

    std::unique_ptr<FormatBuffer> buffer;

    int currentIndent = 0;
    int indentSize = 2;
    bool pretty = false;
};

} // namespace slang