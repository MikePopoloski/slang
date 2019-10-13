//------------------------------------------------------------------------------
// Util.h
// Various utility functions and basic types used throughout the library.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/util/Util.h"

#include <fmt/format.h>

#include "slang/util/SmallVector.h"

#if defined(_MSC_VER)
#    include <Windows.h>
#endif

namespace slang::assert {

[[noreturn]] void assertFailed(const char* expr, const char* file, int line, const char* func) {
    throw AssertionException(fmt::format("Assertion '{}' failed\n  in file {}, line {}\n"
                                         "  function: {}\n",
                                         expr, file, line, func));
}

} // namespace slang::assert

namespace slang {

int editDistance(string_view left, string_view right, bool allowReplacements, int maxDistance) {
    // See: http://en.wikipedia.org/wiki/Levenshtein_distance
    size_t m = left.size();
    size_t n = right.size();

    SmallVectorSized<int, 32> row;
    for (int i = 0; i <= int(n); i++)
        row.append(i);

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

#if defined(_MSC_VER)

std::wstring widen(string_view str) {
    if (str.empty())
        return L"";

    int sz = MultiByteToWideChar(CP_UTF8, 0, str.data(), (int)str.size(), NULL, 0);
    if (sz <= 0)
        throw std::runtime_error("Failed to convert string to UTF16");

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
        throw std::runtime_error("Failed to convert string to UTF8");

    std::string result;
    result.resize(sz);

    WideCharToMultiByte(CP_UTF8, 0, str.data(), (int)str.size(), result.data(), sz, NULL, NULL);
    return result;
}

#endif

} // namespace slang