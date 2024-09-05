//------------------------------------------------------------------------------
// Json.cpp
// Minimal JSON serialization support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/text/Json.h"

#include <climits>

#include "slang/text/FormatBuffer.h"
#include "slang/util/SmallVector.h"
#include "slang/util/String.h"

namespace slang {

JsonWriter::JsonWriter() : buffer(std::make_unique<FormatBuffer>()) {
}

JsonWriter::~JsonWriter() = default;

std::string_view JsonWriter::view() const {
    return std::string_view(buffer->data(), findLastComma());
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

void JsonWriter::writeProperty(std::string_view name) {
    writeQuoted(name);
    buffer->append(":");
    if (pretty)
        buffer->append(" ");
}

void JsonWriter::writeValue(std::string_view value) {
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

void JsonWriter::writeNewLine() {
    buffer->append("\n");
}

void JsonWriter::writeQuoted(std::string_view str) {
    SmallVector<char> vec(str.size() + 2, UninitializedTag());
    vec.push_back('"');
    for (char c : str) {
        switch (c) {
            case '"':
                vec.push_back('\\');
                vec.push_back('"');
                break;
            case '\\':
                vec.push_back('\\');
                vec.push_back('\\');
                break;
            case '\b':
                vec.push_back('\\');
                vec.push_back('b');
                break;
            case '\f':
                vec.push_back('\\');
                vec.push_back('f');
                break;
            case '\n':
                vec.push_back('\\');
                vec.push_back('n');
                break;
            case '\r':
                vec.push_back('\\');
                vec.push_back('r');
                break;
            case '\t':
                vec.push_back('\\');
                vec.push_back('t');
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
                    vec.push_back('\\');
                    vec.push_back('u');
                    vec.append(buf, buf + 4);
                }
                else {
                    // all other characters are added as-is
                    vec.push_back(c);
                }
                break;
        }
    }

    vec.push_back('"');
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
