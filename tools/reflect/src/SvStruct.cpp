// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvStruct.h"

#include "SvType.h"

#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/util/OS.h"

void SvStruct::toCpp(HppFile& hppFile, std::string_view _namespace, const SvAliases& aliases,
                     bool noSystemC) const {
    //* STRUCT DECLARATION **/
    auto structName = isCppReserved(type.name) ? fmt::format("_{}", type.name)
                                               : std::string(type.name);
    hppFile.addWithIndent(fmt::format("struct {} {{\n", structName));
    hppFile.increaseIndent();

    std::vector<std::pair<std::string, SvType>> members;

    size_t structSize = 0;
    if (type.isUnpackedStruct())
        structSize = type.getCanonicalType().as<slang::ast::UnpackedStructType>().bitstreamWidth();
    else
        structSize = type.getCanonicalType().as<slang::ast::PackedStructType>().bitstreamWidth();

    auto cppType = CppType::fromSize(structSize);

    if (cppType == CppType::SC_BV && noSystemC) {
        slang::OS::printE(fmt::format("Headers for the struct {} can not be generated without "
                                      "SystemC support. Please remove the option --no-sc.",
                                      type.name));
        exit(1);
    }

    auto cppTypeStr = structSize > 64 ? fmt::format(fmt::runtime(toString(cppType)), structSize)
                                      : toString(cppType);

    for (const auto& member : type.getCanonicalType().as<slang::ast::Scope>().members()) {
        const auto& variable = member.as<slang::ast::VariableSymbol>();

        auto variableName = isCppReserved(variable.name) ? fmt::format("_{}", variable.name)
                                                         : std::string(variable.name);
        auto typeName = resolveAlias(variable.getType().name, aliases);

        members.emplace_back(variableName, SvType(variable.getType(), typeName));
    }

    std::reverse(members.begin(), members.end());

    //** MEMBERS DECLARATION **//
    for (const auto& member : members) {
        if (member.second.isStructOrEnum() && _namespace != member.second._namespace) {
            hppFile.addWithIndent(fmt::format("{}::{} {};\n", member.second._namespace,
                                              member.second.toString(), member.first));
            hppFile.addIncludeHeader(member.second._namespace);
        }
        else {
            hppFile.addWithIndent(fmt::format("{} {};\n", member.second.toString(), member.first));
        }
    }
    hppFile.add("\n");

    //** GENERATE START AND WIDTH OF EACH SIGNAL **//
    size_t startBit = 0;
    for (const auto& member : members) {
        hppFile.addWithIndent(
            fmt::format("static constexpr size_t {}_s = {};\n", member.first, startBit));
        hppFile.addWithIndent(
            fmt::format("static constexpr size_t {}_w = {};\n", member.first, member.second.size));
        startBit += member.second.size;
    }
    hppFile.addWithIndent(fmt::format("static constexpr size_t _size = {};\n", structSize));
    hppFile.add("\n");

    //** GENERATE DEFAULT CONSTRUCTOR **//
    hppFile.addWithIndent(fmt::format("{}() = default;\n\n", structName));

    //** GENERATE CONSTRUCTOR **//
    {
        hppFile.addWithIndent(fmt::format("{}(", structName));

        hppFile.add(fmt::format("const {}& data) {{\n", cppTypeStr));

        hppFile.increaseIndent();

        std::vector<std::string> values;

        if (structSize > 64) {
            for (const auto& member : members) {
                if (member.second.size == 1)
                    values.emplace_back(fmt::format("data.get_bit({0}_s)", member.first));
                else
                    values.emplace_back(fmt::format(
                        "data.range({0}_s + {0}_w - 1, {0}_s).to_uint64()", member.first));
            }
        }
        else {
            for (const auto& member : members)
                values.emplace_back(fmt::format("(data >> {0}_s) & (~0ULL >> (64 - {1}))",
                                                member.first, member.second.size));
        }

        for (auto i = 0; i < members.size(); i++) {
            const auto& member = members[i];
            const auto& value = values[i];

            if (member.second.isStructOrEnum())
                hppFile.addWithIndent(
                    fmt::format("{} = {}({});\n", member.first, member.second.toString(), value));
            else
                hppFile.addWithIndent(fmt::format("{} = {};\n", member.first, value));
        }

        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n\n");
    }

    //** GENERATE SC_BV CONSTRUCTOR **//
    // Note: This constructor will be generated only if the other constructor is not already from a
    // sc_bv
    if (!noSystemC && structSize <= 64) {
        hppFile.addWithIndent(
            fmt::format("{}(const sc_bv<{}>& data) {{\n", structName, type.bitstreamWidth()));

        hppFile.increaseIndent();

        for (const auto& member : members) {
            std::string value;
            if (member.second.size == 1)
                value = fmt::format("data.get_bit({0}_s)", member.first);
            else
                value = fmt::format("data.range({0}_s + {0}_w - 1, {0}_s).to_uint64()",
                                    member.first);

            if (member.second.isStructOrEnum())
                hppFile.addWithIndent(
                    fmt::format("{} = {}({});\n", member.first, member.second.toString(), value));
            else
                hppFile.addWithIndent(fmt::format("{} = {};\n", member.first, value));
        }

        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n\n");
    }

    //** GENERATE SERIALIZER **//
    if (cppType == CppType::SC_BV) {
        hppFile.addWithIndent(fmt::format("operator {}() const {{\n", cppTypeStr));
        hppFile.increaseIndent();
        hppFile.addWithIndent(fmt::format("auto ret = {}();\n", cppTypeStr));
        for (const auto& member : members) {
            if (member.second.cppType == CppType::BOOL) {
                hppFile.addWithIndent(fmt::format("ret.set_bit({0}_s, {0});\n", member.first));
            }
            else {
                hppFile.addWithIndent(
                    fmt::format("ret.range({0}_s + {0}_w - 1, {0}_s) = ", member.first));
                if (member.second.isStructOrEnum() && member.second.size > 64)
                    hppFile.add(fmt::format("sc_bv<{}>({});\n", member.second.size, member.first));
                else
                    hppFile.add(fmt::format("{};\n", member.first));
            }
        }
        hppFile.addWithIndent("return ret;\n");
    }
    else {
        hppFile.addWithIndent(fmt::format("operator {}() const {{\n", cppTypeStr));
        hppFile.increaseIndent();
        hppFile.addWithIndent(fmt::format("{} ret = 0;\n", cppTypeStr));
        for (const auto& member : members) {
            hppFile.addWithIndent(
                fmt::format("ret |= static_cast<{0}>({1}) << {1}_s;\n", cppTypeStr, member.first));
        }
        hppFile.addWithIndent("return ret;\n");
    }
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    //** GENERATE BV SERIALIZER **//
    if (!noSystemC && cppType != CppType::SC_BV) {
        hppFile.addWithIndent(fmt::format("operator sc_bv<{}>() const {{\n", structSize));
        hppFile.increaseIndent();
        hppFile.addWithIndent(fmt::format("auto ret = sc_bv<{}>();\n", structSize));
        for (const auto& member : members) {
            if (member.second.cppType == CppType::BOOL) {
                hppFile.addWithIndent(fmt::format("ret.set_bit({0}_s, {0});\n", member.first));
            }
            else {
                hppFile.addWithIndent(
                    fmt::format("ret.range({0}_s + {0}_w - 1, {0}_s) = ", member.first));
                if (member.second.isStructOrEnum() && member.second.size > 64)
                    hppFile.add(fmt::format("sc_bv<{}>({});\n", member.second.size, member.first));
                else
                    hppFile.add(fmt::format("{};\n", member.first));
            }
        }
        hppFile.addWithIndent("return ret;\n");
        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n\n");
    }

    //* GENERATE TO STRING FUNCTION *//
    hppFile.addWithIndent("std::string to_string() const {\n");
    hppFile.increaseIndent();
    hppFile.addWithIndent("std::stringstream ss;\n");
    bool first = true;
    for (const auto& member : members) {
        if (first)
            hppFile.addWithIndent(fmt::format("ss << \"{0}\" << \" = \" << ", member.first));
        else
            hppFile.addWithIndent(fmt::format("ss << \" {0}\" << \" = \" << ", member.first));

        if (member.second.cppType == CppType::SC_BV || member.second.cppType == CppType::STRUCT)
            hppFile.add(fmt::format("{0}.to_string();\n", member.first));
        else
            hppFile.add(fmt::format("{0};\n", member.first));

        first = false;
    }
    hppFile.addWithIndent("return std::move(ss.str());\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    //* OVERLOAD << OPERATOR *//
    hppFile.addWithIndent(fmt::format(
        "friend std::ostream& operator<<(std::ostream& os, const {}& data) {{\n", structName));
    hppFile.increaseIndent();
    hppFile.addWithIndent("os << data.to_string();\n");
    hppFile.addWithIndent("return os;\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n");

    //* STATIC GET FUNCTIONS *//
    for (const auto& member : members) {
        hppFile.addWithIndent(fmt::format("static {} get_{} (const {}& data) {{\n",
                                          member.second.toString(), member.first, cppTypeStr));
        hppFile.increaseIndent();
        std::string value;
        if (cppType == CppType::SC_BV)
            value = fmt::format("data.range({0}_s + {0}_w - 1, {0}_s).to_uint64()", member.first);
        else
            value = fmt::format("(data >> {0}_s) & (~0ULL >> (64 - {1}))", member.first,
                                member.second.size);

        if (member.second.isStructOrEnum())
            hppFile.addWithIndent(fmt::format("return {}({});\n", member.second.toString(), value));
        else
            hppFile.addWithIndent(fmt::format("return {};\n", value));

        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n");
    }

    hppFile.decreaseIndent();
    hppFile.addWithIndent("};\n\n");
}
