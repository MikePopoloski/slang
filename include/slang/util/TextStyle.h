//------------------------------------------------------------------------------
//! @file TextStyle.h
//! @brief Terminal text color and style types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>

namespace slang {

/// The set of standard ANSI terminal colors.
enum class TerminalColor {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,
    BrightBlack,
    BrightRed,
    BrightGreen,
    BrightYellow,
    BrightBlue,
    BrightMagenta,
    BrightCyan,
    BrightWhite
};

/// Flags that control text emphasis (font styling) when printed to a terminal.
/// The values can be combined together with a TextStyle.
enum class TextEmphasis : uint8_t {
    /// No emphasis.
    None = 0,
    /// Bold text.
    Bold = 1 << 0,
    /// Faint (decreased intensity) text.
    Faint = 1 << 1,
    /// Italic text.
    Italic = 1 << 2,
    /// Underlined text.
    Underline = 1 << 3,
    /// Blinking text.
    Blink = 1 << 4,
    /// Reversed foreground and background colors.
    Reverse = 1 << 5,
    /// Concealed (hidden) text.
    Conceal = 1 << 6,
    /// Strike-through text.
    Strikethrough = 1 << 7
};

/// A color used for styling terminal text. This is either one of the standard
/// ANSI terminal colors or an arbitrary 24-bit RGB value.
class TextColor {
public:
    /// Constructs an empty color that applies no styling.
    constexpr TextColor() = default;

    /// Constructs a color from one of the standard ANSI terminal colors.
    constexpr TextColor(TerminalColor color) noexcept :
        value_(static_cast<uint32_t>(color)), hasValue_(true), isRgb_(false) {}

    /// @return true if this color specifies any value, otherwise false.
    constexpr bool hasValue() const noexcept { return hasValue_; }

    /// @return true if this color is an RGB value, or false if it is a terminal color.
    constexpr bool isRgb() const noexcept { return isRgb_; }

    /// @return the 24-bit RGB value. Only valid if @a isRgb() is true.
    constexpr uint32_t rgb() const noexcept { return value_; }

    /// @return the terminal color. Only valid if @a isRgb() is false.
    constexpr TerminalColor terminal() const noexcept { return static_cast<TerminalColor>(value_); }

private:
    uint32_t value_ = 0;
    bool hasValue_ = false;
    bool isRgb_ = false;
};

/// Describes the styling (foreground color, background color, and emphasis) to
/// apply to a run of terminal text.
class TextStyle {
public:
    /// Constructs a style with no color and no emphasis.
    constexpr TextStyle() = default;

    /// Constructs a style with the given emphasis and no color.
    constexpr TextStyle(TextEmphasis emphasis) noexcept :
        emphasis_(static_cast<uint8_t>(emphasis)) {}

    /// @return true if a foreground color has been set, otherwise false.
    constexpr bool hasForeground() const noexcept { return foreground_.hasValue(); }

    /// @return true if a background color has been set, otherwise false.
    constexpr bool hasBackground() const noexcept { return background_.hasValue(); }

    /// @return the foreground color. Only valid if @a hasForeground() is true.
    constexpr TextColor foreground() const noexcept { return foreground_; }

    /// @return the background color. Only valid if @a hasBackground() is true.
    constexpr TextColor background() const noexcept { return background_; }

    /// @return the combined emphasis flags as a raw bitmask.
    constexpr uint8_t emphasis() const noexcept { return emphasis_; }

    /// Merges the styling of @a rhs into this style. Colors set in @a rhs take
    /// precedence, and emphasis flags are combined together.
    constexpr TextStyle& operator|=(const TextStyle& rhs) noexcept {
        if (rhs.foreground_.hasValue())
            foreground_ = rhs.foreground_;
        if (rhs.background_.hasValue())
            background_ = rhs.background_;
        emphasis_ = static_cast<uint8_t>(emphasis_ | rhs.emphasis_);
        return *this;
    }

    /// Merges two styles together. See @a operator|=.
    friend constexpr TextStyle operator|(TextStyle lhs, const TextStyle& rhs) noexcept {
        lhs |= rhs;
        return lhs;
    }

    friend constexpr TextStyle fg(TextColor color) noexcept;
    friend constexpr TextStyle bg(TextColor color) noexcept;

private:
    TextColor foreground_;
    TextColor background_;
    uint8_t emphasis_ = 0;
};

/// Creates a text style that sets the given foreground color.
constexpr TextStyle fg(TextColor color) noexcept {
    TextStyle style;
    style.foreground_ = color;
    return style;
}

/// Creates a text style that sets the given background color.
constexpr TextStyle bg(TextColor color) noexcept {
    TextStyle style;
    style.background_ = color;
    return style;
}

} // namespace slang
