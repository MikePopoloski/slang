// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvLocalParam.h"

#include <SvType.h>

static void unwrapUnpackedArray(const std::span<const slang::ConstantValue> constantValues,
                                std::vector<std::vector<uint64_t>>& values,
                                uint64_t& biggestElementSize) {
    if (constantValues.front().isUnpacked())
        for (const auto& unpackedArray : constantValues)
            unwrapUnpackedArray(unpackedArray.elements(), values, biggestElementSize);
    else if (constantValues.front().isInteger()) {
        std::vector<uint64_t> collectedValues;
        for (const auto& value : constantValues) {
            if (!value.isInteger())
                SLANG_THROW(std::runtime_error(
                    "Found a non integer member while reflecting this parameter"));
            if (value.getBitstreamWidth() > 64)
                SLANG_THROW(std::runtime_error(
                    "Found a value bigger than 64 bits while reflecting this parameter"));
            biggestElementSize = std::max(biggestElementSize, value.getBitstreamWidth());
            collectedValues.emplace_back(*value.integer().getRawPtr());
        }
        values.emplace_back(collectedValues);
    }
}

void SvLocalParam::toCpp(HppFile& hppFile, std::string_view, const SvAliases&, bool) const {
    std::string parameterName = isCppReserved(parameter.name) ? fmt::format("_{}", parameter.name)
                                                              : std::string(parameter.name);
    if (parameter.getValue().isUnpacked()) {
        std::vector<std::vector<uint64_t>> unpackedArrays;
        uint64_t biggestSize = 0;
        SLANG_TRY {
            unwrapUnpackedArray(parameter.getValue().elements(), unpackedArrays, biggestSize);
        }
        SLANG_CATCH(const std::runtime_error& error) {
#if __cpp_exceptions
            SLANG_THROW(std::runtime_error(fmt::format(
                "There has been an error while reflecting {}: {}", parameterName, error.what())));
#endif
        }
        if (unpackedArrays.empty())
            SLANG_THROW(std::runtime_error(
                fmt::format("{} has no values, can not reflect.", parameterName)));
        hppFile.addInclude("array");
        auto arraySize = unpackedArrays.front().size();
        auto arrayElementType = toString(CppType::fromSize(biggestSize));
        std::string arrayType = fmt::format("std::array<{}, {}>", arrayElementType, arraySize);
        for (auto i = 1; i < unpackedArrays.size(); i++)
            arrayType = fmt::format("std::array<{}, {}", arrayType, arraySize);
        for (auto i = 1; i < unpackedArrays.size(); i++)
            arrayType += ">";
        hppFile.addWithIndent(
            fmt::format("static constexpr {} {} = {{{{\n", arrayType, parameterName));
        hppFile.increaseIndent();
        for (const auto& unpacked : unpackedArrays) {
            hppFile.addWithIndent("{{");
            for (auto i = 0; i < unpacked.size(); i++) {
                if (i == 0)
                    hppFile.add(fmt::format(" {:#x}", unpacked[i]));
                else
                    hppFile.add(fmt::format(", {:#x}", unpacked[i]));
            }
            hppFile.add(" }},\n");
        }
        hppFile.decreaseIndent();
        hppFile.addWithIndent("}};\n");
    }
    else if (parameter.getValue().isInteger()) {
        hppFile.addWithIndent(
            fmt::format("static constexpr {} {} = {};\n",
                        toString(CppType::fromSize(parameter.getType().getBitstreamWidth())),
                        parameterName, *parameter.getValue().integer().getRawPtr()));
    }
    else {
        SLANG_THROW(
            std::runtime_error(fmt::format("Can't reflect this localparam {}", parameterName)));
    }
}
