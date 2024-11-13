// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvUnion.h"

#include <SvType.h>
#include <fmt/format.h>
#include <set>
#include <slang/ast/symbols/VariableSymbols.h>
#include <slang/util/OS.h>

void SvUnion::toCpp(HppFile& hppFile, std::string_view _namespace, const SvAliases& aliases,
                    const bool noSystemC) const {
    //* UNION DECLARATION **/
    auto unionName = isCppReserved(type.name) ? fmt::format("_{}", type.name)
                                              : std::string(type.name);
    hppFile.addWithIndent(fmt::format("struct {} {{\n", unionName));
    hppFile.increaseIndent();

    std::vector<std::pair<std::string, SvType>> members;

    const size_t unionSize = type.getBitstreamWidth();
    const auto cppType = CppType::fromSize(unionSize);
    hppFile.addWithIndent(fmt::format("static constexpr size_t _size = {};\n\n", unionSize));

    if (cppType == CppType::SC_BV && noSystemC) {
        slang::OS::printE(fmt::format("Headers for the union {} can not be generated without "
                                      "SystemC support. Please remove the option --no-sc.",
                                      type.name));
        exit(1);
    }

    auto cppTypeStr = unionSize > 64 ? format(fmt::runtime(toString(cppType)), unionSize)
                                     : toString(cppType);

    // Create a sc bit vector to store the data of the Union
    hppFile.addWithIndent(fmt::format("{} union_data;\n\n", cppTypeStr));

    // Check if some headers need to be included
    for (const auto& member : type.getCanonicalType().as<slang::ast::Scope>().members()) {
        const auto& variable = member.as<slang::ast::VariableSymbol>();

        const auto variableName = isCppReserved(variable.name) ? fmt::format("_{}", variable.name)
                                                               : std::string(variable.name);
        const auto typeName = resolveAlias(variable.getType().name, aliases);

        const auto variableType = SvType(variable.getType(), typeName);
        if (variableType.isStructEnumOrUnion() && _namespace != variableType._namespace)
            hppFile.addIncludeHeader(variableType._namespace);

        members.emplace_back(variableName, variableType);
    }

    //** GENERATE DEFAULT CONSTRUCTOR **//
    hppFile.addWithIndent(fmt::format("{}() = default;\n\n", unionName));

    //** GENERATE CONSTRUCTOR **//
    {
        hppFile.addWithIndent(fmt::format("{}(const {}& __data) {{\n", unionName, cppTypeStr));

        hppFile.increaseIndent();

        hppFile.addWithIndent("union_data = __data;\n");

        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n\n");
    }

    //** GENERATE SC_BV CONSTRUCTOR **//
    // Note: This constructor will be generated only if the other constructor is not already
    // from a sc_bv
    if (!noSystemC && unionSize <= 64) {
        hppFile.addWithIndent(
            fmt::format("{}(const sc_bv<{}>& __data) {{\n", unionName, type.getBitstreamWidth()));

        hppFile.increaseIndent();

        hppFile.addWithIndent("union_data = __data.to_uint64();\n");

        hppFile.decreaseIndent();
        hppFile.addWithIndent("}\n\n");
    }

    //** GENERATE SERIALIZERS **//

    // Base serializer for the inner type of the Union
    if (cppType == CppType::SC_BV) {
        hppFile.addWithIndent(fmt::format("operator {}() const {{\n", cppTypeStr));
        hppFile.increaseIndent();
        hppFile.addWithIndent(fmt::format("return sc_bv<{}>(union_data);\n", unionSize));
    }
    else {
        hppFile.addWithIndent(fmt::format("operator {}() const {{\n", cppTypeStr));
        hppFile.increaseIndent();
        hppFile.addWithIndent("return union_data;\n");
    }

    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    // Other serializers for the different types of the union members
    if (!members.empty()) {
        std::set memberTypes = {cppTypeStr};
        for (const auto& [_, memberType] : members) {
            auto memberTypeName = memberType.toString();

            // Skip the serializer for this member if the type serializer has already been generated
            if (memberTypes.contains(memberTypeName))
                continue;
            memberTypes.insert(memberTypeName);

            if (_namespace != memberType._namespace)
                hppFile.addWithIndent(fmt::format("operator {}::{}() const {{\n",
                                                  memberType._namespace, memberTypeName));
            else
                hppFile.addWithIndent(fmt::format("operator {}() const {{\n", memberTypeName));

            hppFile.increaseIndent();

            constexpr auto unionVariable = "union_data"sv;

            if (memberType.isStructEnumOrUnion()) {
                if (_namespace != memberType._namespace)
                    hppFile.addWithIndent(fmt::format("return {}::{}({});\n", memberType._namespace,
                                                      memberTypeName, unionVariable));
                else
                    hppFile.addWithIndent(
                        fmt::format("return {}({});\n", memberTypeName, unionVariable));
            }
            else {
                if (unionSize > 64)
                    hppFile.addWithIndent(fmt::format("return {};\n", unionVariable));
                else
                    hppFile.addWithIndent(fmt::format("return static_cast<{}>({});\n",
                                                      memberTypeName, unionVariable));
            }

            hppFile.decreaseIndent();
            hppFile.addWithIndent("}\n\n");
        }
    }

    //** GENERATE EXPLICIT FUNCTIONS TO GET THE DIFFERENT UNION MEMBERS **//
    if (!members.empty()) {
        for (const auto& [memberName, memberType] : members) {
            auto memberTypeName = memberType.toString();

            if (_namespace != memberType._namespace)
                hppFile.addWithIndent(fmt::format("{}::{} {}() const {{\n", memberType._namespace,
                                                  memberTypeName, memberName));
            else
                hppFile.addWithIndent(
                    fmt::format("{} {}() const {{\n", memberTypeName, memberName));

            hppFile.increaseIndent();

            constexpr auto unionVariable = "union_data"sv;

            if (memberType.isStructEnumOrUnion()) {
                if (_namespace != memberType._namespace)
                    hppFile.addWithIndent(fmt::format("return {}::{}({});\n", memberType._namespace,
                                                      memberTypeName, unionVariable));
                else
                    hppFile.addWithIndent(
                        fmt::format("return {}({});\n", memberTypeName, unionVariable));
            }
            else {
                if (unionSize > 64)
                    hppFile.addWithIndent(fmt::format("return {};\n", unionVariable));
                else
                    hppFile.addWithIndent(fmt::format("return static_cast<{}>({});\n",
                                                      memberTypeName, unionVariable));
            }

            hppFile.decreaseIndent();
            hppFile.addWithIndent("}\n\n");
        }
    }

    //* GENERATE TO STRING FUNCTION *//
    hppFile.addWithIndent("std::string to_string() const {\n");
    hppFile.increaseIndent();
    hppFile.addWithIndent("std::stringstream ss;\n");
    bool first = true;
    for (const auto& [memberName, memberType] : members) {
        if (first)
            hppFile.addWithIndent(fmt::format("ss << \"{0}\" << \" = \" << ", memberName));
        else
            hppFile.addWithIndent(fmt::format("ss << \" {0}\" << \" = \" << ", memberName));

        if (memberType.cppType == CppType::SC_BV)
            hppFile.add(fmt::format("static_cast<{}::{}>(*this).to_string();\n",
                                    memberType._namespace, memberType.name, memberName));
        else
            hppFile.add(fmt::format("static_cast<{}::{}>(*this);\n", memberType._namespace,
                                    memberType.name, memberName));

        first = false;
    }
    hppFile.addWithIndent("return std::move(ss.str());\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n\n");

    //* OVERLOAD << OPERATOR *//
    hppFile.addWithIndent(fmt::format(
        "friend std::ostream& operator<<(std::ostream& os, const {}& __data) {{\n", unionName));
    hppFile.increaseIndent();
    hppFile.addWithIndent("os << __data.to_string();\n");
    hppFile.addWithIndent("return os;\n");
    hppFile.decreaseIndent();
    hppFile.addWithIndent("}\n");

    hppFile.decreaseIndent();
    hppFile.addWithIndent("};\n\n");
}
