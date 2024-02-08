//------------------------------------------------------------------------------
//! @file Json.h
//! @brief Minimal JSON serialization support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "slang/util/Util.h"

namespace slang {

class FormatBuffer;

/// A very lightweight JSON writer.
///
/// This class is simple and has few features; it's expected that you'll
/// call its methods in the correct order to generate valid JSON. If not,
/// it will happily spit out unparseable text.
class SLANG_EXPORT JsonWriter {
public:
    JsonWriter();
    ~JsonWriter();

    /// Sets the number of spaces to indent whenever opening a new
    /// level of structure in the JSON.
    void setIndentSize(int size) { indentSize = size; }

    /// Set whether pretty printing is enabled (off by default).
    /// When pretty printing is on, newlines, additional whitespace,
    /// and indentation are added to make the output more human friendly.
    void setPrettyPrint(bool enabled) { pretty = enabled; }

    /// @return a view of the emitted JSON text so far.
    /// @note the returned view is not guaranteed to remain valid once
    /// additional writes are performed.
    std::string_view view() const;

    /// Begins a new JSON object. It's expected that you will write zero or
    /// more properties and then end the object.
    void startObject();

    /// Ends the currently active object. Output will be messed up
    /// if there is no active object.
    void endObject();

    /// Begins a new JSON array. It's expected that you will write zero or
    /// more values and then end the array.
    void startArray();

    /// Ends the currently active array. Output will be messed up
    /// if there is no active object.
    void endArray();

    /// Writes an object property with the given name. It's expected that you
    /// will immediately write some kind of value for the property.
    void writeProperty(std::string_view name);

    /// Writes an array or property string value.
    void writeValue(std::string_view value);

    /// Writes an array or property signed integer value.
    void writeValue(int64_t value);

    /// Writes an array or property unsigned integer value.
    void writeValue(uint64_t value);

    /// Writes an array or property floating point value.
    void writeValue(double value);

    /// Writes an array or property boolean value ("true" or "false").
    void writeValue(bool value);

    /// Writes a newline character into the buffer.
    void writeNewLine();

private:
    void endValue();
    size_t findLastComma() const;
    void writeQuoted(std::string_view str);

    std::unique_ptr<FormatBuffer> buffer;

    int currentIndent = 0;
    int indentSize = 2;
    bool pretty = false;
};

} // namespace slang
