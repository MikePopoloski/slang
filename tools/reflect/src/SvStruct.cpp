// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvStruct.h"

#include "SvType.h"

#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/util/OS.h"

void SvStruct::toCpp(HppFile& hppFile, const std::string_view _namespace, const SvAliases& aliases,
                     const bool noSystemC) const {
    //* STRUCT DECLARATION **/
    auto structName = isCppReserved(type.name) ? fmt::format("_{}", type.name)
                                               : std::string(type.name);
    hppFile.addWithIndent(fmt::format("struct {} {{\n", structName));
    hppFile.increaseIndent();

    std::vector<std::pair<std::string, SvType>> members;

    const size_t structSize = type.getBitstreamWidth();
    const auto cppType = CppType::fromSize(structSize);

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

    std::ranges::reverse(members);

    //** MEMBERS DECLARATION **//
    for (const auto& [name, type] : members) {
        if (type.isStructEnumOrUnion() && _namespace != type._namespace) {
            hppFile.addWithIndent(
                fmt::format("{}::{} {};\n", type._namespace, type.toString(), name));
            hppFile.addIncludeHeader(type._namespace);
        }
        else {
            hppFile.addWithIndent(fmt::format("{} {};\n", type.toString(), name));
        }
    }
    hppFile.add("\n");

    //** GENERATE START AND WIDTH OF EACH SIGNAL **//
    size_t startBit = 0;
    for (const auto& [name, type] : members) {
        hppFile.addWithIndent(fmt::format("static constexpr size_t {}_s = {};\n", name, startBit));
        hppFile.addWithIndent(fmt::format("static constexpr size_t {}_w = {};\n", name, type.size));
        startBit += type.size;
    }
    hppFile.addWithIndent(fmt::format("static constexpr size_t _size = {};\n", structSize));
    hppFile.add("\n");

    //** GENERATE DEFAULT CONSTRUCTOR **//
    hppFile.addWithIndent(fmt::format("{}() = default;\n\n", structName));

    //** GENERATE CONSTRUCTOR **//
    {
        hppFile.addWithIndent(fmt::format("{}(", structName));

        hppFile.add(fmt::format("const {}& __data) {{\n", cppTypeStr));

        hppFile.increaseIndent();

        std::vector<std::string> values;

        if (structSize > 64) {
            for (const auto& [name, type] : members) {
                if (type.size == 1)
                    values.emplace_back(fmt::format("__data.get_bit({0}_s)", name));
                else if (type.size > 64)
                    values.emplace_back(
                        fmt::format("__data.range({0}_s + {0}_w - 1, {0}_s)", name));
                else
                    values.emplace_back(
                        fmt::format("__data.range({0}_s + {0}_w - 1, {0}_s).to_uint64()", name));
            }
        }
        else {
            for (const auto& [name, type] : members)
                values.emplace_back(
                    fmt::format("(__data >> {0}_s) & (~0ULL >> (64 - {1}))", name, type.size));
        }

        for (auto i = 0; i < members.size(); i++) {
            const auto& [name, type] = members[i];
            const auto& value = values[i];

            if (type.isStructEnumOrUnion())
                if (_namespace != type._namespace)
                    hppFile.addWithIndent(fmt::format("{} = {}::{}({});\n", name, type._namespace,
                                                      type.toString(), value));
                else
                    hppFile.addWithIndent(
                        fmt::format("{} = {}({});\n", name, type.toString(), value));
            else
                hppFile.addWithIndent(fmt::format("{} = {};\n", name, value));
        }

        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n\n");
    }

    //** GENERATE SC_BV CONSTRUCTOR **//
    // Note: This constructor will be generated only if the other constructor is not already from a
    // sc_bv
    if (!noSystemC && structSize <= 64) {
        hppFile.addWithIndent(
            fmt::format("{}(const sc_bv<{}>& __data) {{\n", structName, type.getBitstreamWidth()));

        hppFile.increaseIndent();

        for (const auto& [name, type] : members) {
            std::string value;
            if (type.size == 1)
                value = fmt::format("__data.get_bit({0}_s)", name);
            else
                value = fmt::format("__data.range({0}_s + {0}_w - 1, {0}_s).to_uint64()", name);

            if (type.isStructEnumOrUnion())
                if (_namespace != type._namespace)
                    hppFile.addWithIndent(fmt::format("{} = {}::{}({});\n", name, type._namespace,
                                                      type.toString(), value));
                else
                    hppFile.addWithIndent(
                        fmt::format("{} = {}({});\n", name, type.toString(), value));
            else
                hppFile.addWithIndent(fmt::format("{} = {};\n", name, value));
        }

        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n\n");
    }

    //** GENERATE SERIALIZER **//
    if (cppType == CppType::SC_BV) {
        hppFile.addWithIndent(fmt::format("operator {}() const {{\n", cppTypeStr));
        hppFile.increaseIndent();
        hppFile.addWithIndent(fmt::format("auto ret = {}();\n", cppTypeStr));
        for (const auto& [name, type] : members) {
            if (type.cppType == CppType::BOOL) {
                hppFile.addWithIndent(fmt::format("ret.set_bit({0}_s, {0});\n", name));
            }
            else {
                hppFile.addWithIndent(fmt::format("ret.range({0}_s + {0}_w - 1, {0}_s) = ", name));
                if (type.isStructEnumOrUnion() && type.size > 64)
                    hppFile.add(fmt::format("sc_bv<{}>({});\n", type.size, name));
                else
                    hppFile.add(fmt::format("{};\n", name));
            }
        }
        hppFile.addWithIndent("return ret;\n");
    }
    else {
        hppFile.addWithIndent(fmt::format("operator {}() const {{\n", cppTypeStr));
        hppFile.increaseIndent();
        hppFile.addWithIndent(fmt::format("{} ret = 0;\n", cppTypeStr));
        for (const auto& name : members | std::views::keys) {
            hppFile.addWithIndent(
                fmt::format("ret |= static_cast<{0}>({1}) << {1}_s;\n", cppTypeStr, name));
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
        for (const auto& [name, type] : members) {
            if (type.cppType == CppType::BOOL) {
                hppFile.addWithIndent(fmt::format("ret.set_bit({0}_s, {0});\n", name));
            }
            else {
                hppFile.addWithIndent(fmt::format("ret.range({0}_s + {0}_w - 1, {0}_s) = ", name));
                if (type.isStructEnumOrUnion() && type.size > 64)
                    hppFile.add(fmt::format("sc_bv<{}>({});\n", type.size, name));
                else
                    hppFile.add(fmt::format("{};\n", name));
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
    for (const auto& [name, type] : members) {
        if (first)
            hppFile.addWithIndent(fmt::format("ss << \"{0}\" << \" = \" << ", name));
        else
            hppFile.addWithIndent(fmt::format("ss << \" {0}\" << \" = \" << ", name));

        if (type.cppType == CppType::SC_BV || type.cppType == CppType::STRUCT)
            hppFile.add(fmt::format("{0}.to_string();\n", name));
        else
            hppFile.add(fmt::format("{0};\n", name));

        first = false;
    }
    hppFile.addWithIndent("return std::move(ss.str());\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    //* OVERLOAD << OPERATOR *//
    hppFile.addWithIndent(fmt::format(
        "friend std::ostream& operator<<(std::ostream& os, const {}& __data) {{\n", structName));
    hppFile.increaseIndent();
    hppFile.addWithIndent("os << __data.to_string();\n");
    hppFile.addWithIndent("return os;\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n");

    //* STATIC GET FUNCTIONS *//
    for (const auto& [name, type] : members) {
        if (type.isStructEnumOrUnion() && _namespace != type._namespace) {
            hppFile.addWithIndent(fmt::format("static {}::{} get_{} (const {}& __data) {{\n",
                                              type._namespace, type.toString(), name, cppTypeStr));
        }
        else {
            hppFile.addWithIndent(fmt::format("static {} get_{} (const {}& __data) {{\n",
                                              type.toString(), name, cppTypeStr));
        }
        hppFile.increaseIndent();
        std::string value;
        if (cppType == CppType::SC_BV) {
            if (type.size == 1)
                value = fmt::format("__data.get_bit({0}_s)", name);
            else if (type.size > 64)
                value = fmt::format("__data.range({0}_s + {0}_w - 1, {0}_s)", name);
            else
                value = fmt::format("__data.range({0}_s + {0}_w - 1, {0}_s).to_uint64()", name);
        }
        else {
            value = fmt::format("(__data >> {0}_s) & (~0ULL >> (64 - {1}))", name, type.size);
        }

        if (type.isStructEnumOrUnion())
            if (_namespace != type._namespace)
                hppFile.addWithIndent(
                    fmt::format("return {}::{}({});\n", type._namespace, type.toString(), value));
            else
                hppFile.addWithIndent(fmt::format("return {}({});\n", type.toString(), value));
        else
            hppFile.addWithIndent(fmt::format("return {};\n", value));

        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n");
    }

    hppFile.decreaseIndent();
    hppFile.addWithIndent("};\n\n");
}
