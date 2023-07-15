//------------------------------------------------------------------------------
// String.cpp
// Various string utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/String.h"

#include <charconv>
#include <string>

#include "slang/util/SmallVector.h"

#if defined(_WIN32)
#    ifndef WIN32_LEAN_AND_MEAN
#        define WIN32_LEAN_AND_MEAN
#    endif
#    ifndef NOMINMAX
#        define NOMINMAX
#    endif
#    include <Windows.h>
#endif

namespace slang {

template<typename T>
void uintToStrImpl(SmallVectorBase<char>& buffer, const char* format, T value) {
    size_t sz = (size_t)snprintf(nullptr, 0, format, value);
    size_t offset = buffer.size();
    buffer.resize(buffer.size() + sz + 1);

    snprintf(&buffer[offset], sz + 1, format, value);
    buffer.pop_back();
}

void uintToStr(SmallVectorBase<char>& buffer, uint32_t value) {
    uintToStrImpl(buffer, "%u", value);
}

void uintToStr(SmallVectorBase<char>& buffer, uint64_t value) {
    uintToStrImpl(buffer, "%lu", value);
}

std::optional<int32_t> strToInt(std::string_view str, size_t* pos, int base) {
    int32_t value;
    auto result = std::from_chars(str.data(), str.data() + str.size(), value, base);
    if (result.ec != std::errc())
        return std::nullopt;

    if (pos)
        *pos = size_t(result.ptr - str.data());
    return value;
}

std::optional<uint32_t> strToUInt(std::string_view str, size_t* pos, int base) {
    uint32_t value;
    auto result = std::from_chars(str.data(), str.data() + str.size(), value, base);
    if (result.ec != std::errc())
        return std::nullopt;

    if (pos)
        *pos = size_t(result.ptr - str.data());
    return value;
}

// TODO: improve this once std::from_chars is available everywhere
std::optional<double> strToDouble(std::string_view str, size_t* pos) {
    std::string copy(str);
    const char* start = copy.c_str();

    char* end;
    errno = 0;
    double val = strtod(start, &end);

    if (start == end || errno == ERANGE)
        return std::nullopt;

    if (pos)
        *pos = size_t(end - start);
    return val;
}

void strToUpper(std::string& str) {
    std::ranges::transform(str, str.begin(), [](char c) { return charToUpper(c); });
}

void strToLower(std::string& str) {
    std::ranges::transform(str, str.begin(), [](char c) { return charToLower(c); });
}

int editDistance(std::string_view left, std::string_view right, bool allowReplacements,
                 int maxDistance) {
    // See: http://en.wikipedia.org/wiki/Levenshtein_distance
    size_t m = left.size();
    size_t n = right.size();

    SmallVector<int, 32> row(n, UninitializedTag());
    for (int i = 0; i <= int(n); i++)
        row.push_back(i);

    for (size_t y = 1; y <= m; y++) {
        row[0] = int(y);
        int best = row[0];

        int prev = int(y - 1);
        for (size_t x = 1; x <= n; x++) {
            int old = row[x];
            if (allowReplacements) {
                row[x] = std::min(prev + (left[y - 1] == right[x - 1] ? 0 : 1),
                                  std::min(row[x - 1], row[x]) + 1);
            }
            else {
                if (left[y - 1] == right[x - 1])
                    row[x] = prev;
                else
                    row[x] = std::min(row[x - 1], row[x]) + 1;
            }

            prev = old;
            best = std::min(best, row[x]);
        }

        if (maxDistance && best > maxDistance)
            return maxDistance + 1;
    }

    return row[n];
}

std::string getU8Str(const std::filesystem::path& path) {
    return std::string(narrow(path.native()));
}

#if defined(_WIN32)

std::wstring widen(std::string_view str) {
    if (str.empty())
        return L"";

    int sz = MultiByteToWideChar(CP_UTF8, 0, str.data(), (int)str.size(), NULL, 0);
    if (sz <= 0)
        SLANG_THROW(std::runtime_error("Failed to convert string to UTF16"));

    std::wstring result;
    result.resize(sz);

    MultiByteToWideChar(CP_UTF8, 0, str.data(), (int)str.length(), result.data(), sz);
    return result;
}

std::string narrow(std::wstring_view str) {
    if (str.empty())
        return "";

    int sz = WideCharToMultiByte(CP_UTF8, 0, str.data(), (int)str.size(), NULL, 0, NULL, NULL);
    if (sz <= 0)
        SLANG_THROW(std::runtime_error("Failed to convert string to UTF8"));

    std::string result;
    result.resize(sz);

    WideCharToMultiByte(CP_UTF8, 0, str.data(), (int)str.size(), result.data(), sz, NULL, NULL);
    return result;
}

#endif

} // namespace slang
