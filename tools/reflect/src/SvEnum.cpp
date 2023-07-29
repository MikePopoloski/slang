// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvEnum.h"

#include <fmt/format.h>
#include <iostream>

void SvEnum::toCpp(HppFile& hppFile, std::string_view, const SvAliases&, bool) const {
    auto underlyingType = [&]() {
        if (type.bitstreamWidth() <= 8)
            return "uint8_t"sv;
        if (type.bitstreamWidth() <= 16)
            return "uint16_t"sv;
        if (type.bitstreamWidth() <= 32)
            return "uint32_t"sv;
        if (type.bitstreamWidth() <= 64)
            return "uint64_t"sv;
        else
            SLANG_THROW(
                std::runtime_error("Enum with $bits size bigger than 64 bits are not supported"));
    };
    //** STRUCT (ENUM) DECLARATION **//
    hppFile.addWithIndent(fmt::format("struct {} {{\n", type.name));
    hppFile.increaseIndent();

    hppFile.addWithIndent(fmt::format("enum Type : {} {{\n", underlyingType()));
    hppFile.increaseIndent();

    std::vector<std::pair<std::string, uint64_t>> members;

    for (const auto& member : type.getCanonicalType().as<slang::ast::Scope>().members()) {
        const auto& enumMember = member.as<slang::ast::EnumValueSymbol>();
        std::string enumName = isCppReserved(enumMember.name) ? fmt::format("_{}", enumMember.name)
                                                              : std::string(enumMember.name);
        members.emplace_back(enumName, *enumMember.getValue().integer().getRawPtr());
    }

    //** MEMBERS DECLARATION **//
    for (auto i = 0; i < members.size(); i++) {
        hppFile.addWithIndent(fmt::format("{} = {}", members[i].first, members[i].second));
        if (i == members.size() - 1)
            hppFile.add("\n");
        else
            hppFile.add(",\n");
    }
    hppFile.decreaseIndent();
    hppFile.addWithIndent("};\n\n");

    //** SIZE **/
    hppFile.addWithIndent(
        fmt::format("static constexpr size_t _size = {};\n\n", type.bitstreamWidth()));

    //** LOCAL **//
    hppFile.addWithIndent("Type type;\n");

    //** DEFAULT CONSTRUCTOR **//
    hppFile.addWithIndent(fmt::format("{}() = default;\n", type.name));

    //** CONSTRUCTOR **//
    hppFile.addWithIndent(fmt::format("{} ({} data) {{\n", type.name, underlyingType()));
    hppFile.increaseIndent();
    hppFile.addWithIndent("switch (data) {\n");
    hppFile.increaseIndent();
    for (const auto& member : members)
        hppFile.addWithIndent(
            fmt::format("case {}: type = Type::{}; break;\n", member.second, member.first));
    hppFile.addWithIndent(fmt::format(
        "default: throw std::runtime_error(\"Can not create {} from provided value\");\n",
        type.name));
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    //** CONSTRUCTOR FROM ENUM **//
    hppFile.addWithIndent(fmt::format("{0} (Type& type) {{ this->type = type; }}\n", type.name));

    //** OVERLOAD << OPERATOR **//
    hppFile.addWithIndent(fmt::format(
        "friend std::ostream& operator<<(std::ostream& os, const {}& data) {{\n", type.name));
    hppFile.increaseIndent();
    hppFile.addWithIndent("switch (data.type) {\n");
    hppFile.increaseIndent();
    for (const auto& member : members)
        hppFile.addWithIndent(fmt::format("case Type::{0}: os << \"{0}\"; break;\n", member.first));
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n");
    hppFile.addWithIndent("return os;\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    //** OVERLOAD = OPERATOR **//
    hppFile.addWithIndent(fmt::format("{}& operator=(const Type t) {{\n", type.name));
    hppFile.increaseIndent();
    hppFile.addWithIndent("this->type = t;\n");
    hppFile.addWithIndent("return *this;\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    //** OVERLOAD UINT64_T OPERATOR **//
    hppFile.addWithIndent(fmt::format("operator uint64_t() const {{\n"));
    hppFile.increaseIndent();
    hppFile.addWithIndent(fmt::format("return static_cast<uint64_t>(type);\n", type.name));
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    //** OVERLOAD () OPERATOR **//
    hppFile.addWithIndent(fmt::format("Type operator() () const {{\n"));
    hppFile.increaseIndent();
    hppFile.addWithIndent("return type;\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    hppFile.decreaseIndent();
    hppFile.addWithIndent("};\n\n");
}
