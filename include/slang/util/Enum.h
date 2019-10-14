//------------------------------------------------------------------------------
// Enum.h
// Various enum utilities.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#define UTIL_ENUM_ELEMENT(x) x,
#define UTIL_ENUM_STRING(x) #x,
#define ENUM(name, elements)                                           \
    enum class name { elements(UTIL_ENUM_ELEMENT) };                   \
    inline string_view toString(name e) {                              \
        static const char* strings[] = { elements(UTIL_ENUM_STRING) }; \
        return strings[static_cast<std::underlying_type_t<name>>(e)];  \
    }                                                                  \
    inline std::ostream& operator<<(std::ostream& os, name e) { return os << toString(e); }

#define ENUM_MEMBER(name, elements)                                    \
    enum name { elements(UTIL_ENUM_ELEMENT) };                         \
    friend string_view toString(name e) {                              \
        static const char* strings[] = { elements(UTIL_ENUM_STRING) }; \
        return strings[static_cast<std::underlying_type_t<name>>(e)];  \
    }