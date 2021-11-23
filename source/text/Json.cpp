//------------------------------------------------------------------------------
// Json.cpp
// Minimal JSON serialization support
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include <climits>

#include "slang/text/Json.h"

#include "FormatBuffer.h"

#include "slang/util/SmallVector.h"
#include "slang/util/String.h"

namespace slang {

JsonWriter::JsonWriter() : buffer(std::make_unique<FormatBuffer>()) {
}

JsonWriter::~JsonWriter() = default;

string_view JsonWriter::view() const {
    return string_view(buffer->data(), findLastComma());
}

void JsonWriter::startObject() {
    buffer->append("{");
    if (pretty) {
        currentIndent += indentSize;
        buffer->format("\n{:{}}", "", currentIndent);
    }
}

void JsonWriter::endObject() {
    buffer->resize(findLastComma());
    if (pretty) {
        currentIndent -= indentSize;
        buffer->format("\n{:{}}}}", "", currentIndent);
        endValue();
    }
    else {
        buffer->append("},");
    }
}

void JsonWriter::startArray() {
    buffer->append("[");
    if (pretty) {
        currentIndent += indentSize;
        buffer->format("\n{:{}}", "", currentIndent);
    }
}

void JsonWriter::endArray() {
    buffer->resize(findLastComma());
    if (pretty) {
        currentIndent -= indentSize;
        buffer->format("\n{:{}}]", "", currentIndent);
        endValue();
    }
    else {
        buffer->append("],");
    }
}

void JsonWriter::writeProperty(string_view name) {
    writeQuoted(name);
    buffer->append(":");
    if (pretty)
        buffer->append(" ");
}

void JsonWriter::writeValue(string_view value) {
    writeQuoted(value);
    endValue();
}

void JsonWriter::writeValue(int64_t value) {
    buffer->format("{}", value);
    endValue();
}

void JsonWriter::writeValue(uint64_t value) {
    buffer->format("{}", value);
    endValue();
}

void JsonWriter::writeValue(double value) {
    buffer->format("{}", value);
    endValue();
}

void JsonWriter::writeValue(bool value) {
    buffer->append(value ? "true" : "false");
    endValue();
}

void JsonWriter::writeQuoted(string_view str) {
    SmallVectorSized<char, 32> vec(str.size() + 2);
    vec.append('"');
    for (char c : str) {
        switch (c) {
            case '"':
                vec.append('\\');
                vec.append('"');
                break;
            case '\\':
                vec.append('\\');
                vec.append('\\');
                break;
            case '\b':
                vec.append('\\');
                vec.append('b');
                break;
            case '\f':
                vec.append('\\');
                vec.append('f');
                break;
            case '\n':
                vec.append('\\');
                vec.append('n');
                break;
            case '\r':
                vec.append('\\');
                vec.append('r');
                break;
            case '\t':
                vec.append('\\');
                vec.append('t');
                break;
            default:
#if CHAR_MIN < 0
                if (c >= 0x00 and c <= 0x1f) {
#else
                if (c <= 0x1f) {
#endif
                    // print character c as \uxxxx
                    char buf[5];
                    snprintf(buf, sizeof(buf), "%04x", int(c));
                    vec.append('\\');
                    vec.append('u');
                    vec.appendRange(buf, buf + 4);
                }
                else {
                    // all other characters are added as-is
                    vec.append(c);
                }
                break;
        }
    }

    vec.append('"');
    buffer->append(toStringView(vec));
}

void JsonWriter::endValue() {
    buffer->append(",");
    if (pretty)
        buffer->format("\n{:{}}", "", currentIndent);
}

size_t JsonWriter::findLastComma() const {
    size_t size = buffer->size();
    if (pretty) {
        while (size && (buffer->data()[size - 1] == ' ' || buffer->data()[size - 1] == '\n'))
            size--;
    }

    if (size && buffer->data()[size - 1] == ',')
        size--;

    return size;
}

} // namespace slang