// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvTypeReflector.h"

#include "ASTVisitors.h"
#include "SvEnum.h"
#include "SvGeneric.h"
#include "SvLocalParam.h"
#include "SvStruct.h"
#include "fmt/color.h"

#include "slang/util/OS.h"

using namespace slang;
using namespace ast;

void SvTypeReflector::reflect() {
    auto checkPublic = [](const auto& type, auto tokenKind) {
        static auto visitor = PublicDirectiveVisitor(tokenKind);
        if (!type.getSyntax())
            return false;
        type.getSyntax()->visit(visitor);
        return visitor();
    };

    auto getNamespace = [](const auto& type) {
        if (const auto parent = type.getHierarchicalParent(); parent)
            return parent->asSymbol().name;
        else
            return "top"sv;
    };

    struct namespaceMembers {
        std::vector<std::unique_ptr<SvGeneric>> members;
        SvAliases aliases;
    };
    std::unordered_map<std::string_view, namespaceMembers> namespaces;

    compilation->getRoot().visit(makeVisitor([&](auto&, const TypeAliasType& type) {
        if (checkPublic(type, slang::parsing::TokenKind::Semicolon)) {
            if (type.isStruct())
                namespaces[getNamespace(type)].members.emplace_back(
                    std::make_unique<SvStruct>(type));
            else if (type.isEnum())
                namespaces[getNamespace(type)].members.emplace_back(std::make_unique<SvEnum>(type));
            if (verbose)
                OS::print(fmt::fg(fmt::color::yellow_green),
                          fmt::format("Detected {} as public\n", type.name));
        }

        if (type.isAlias() && type.targetType.getType().name != "")
            namespaces[getNamespace(type)].aliases[type.name] = type.targetType.getType().name;
    }));

    compilation->getRoot().visit(makeVisitor([&](auto&, const ParameterSymbol& type) {
        if (type.isLocalParam() && checkPublic(type, parsing::TokenKind::Equals)) {
            namespaces[getNamespace(type)].members.emplace_back(
                std::make_unique<SvLocalParam>(type));
            if (verbose)
                OS::print(fmt::fg(fmt::color::yellow_green),
                          fmt::format("Detected {} as public\n", type.name));
        }
    }));

    for (const auto& _namespace : namespaces) {
        if (_namespace.second.members.empty())
            continue;

        //** NAMESPACE DECLARATION **//
        auto& hpp = cppEmitter.newNamespace(_namespace.first);
        hpp.add(fmt::format("namespace {} {{\n", _namespace.first));
        hpp.increaseIndent();

        //** NAMESPACE MEMBERS DECLARATION **//
        for (const auto& generic : _namespace.second.members) {
            if (generic->isStruct())
                reinterpret_cast<SvStruct*>(generic.get())
                    ->toCpp(hpp, _namespace.first, _namespace.second.aliases, noSystemC);
            else if (generic->isEnum())
                reinterpret_cast<SvEnum*>(generic.get())
                    ->toCpp(hpp, _namespace.first, _namespace.second.aliases, noSystemC);
            else if (generic->isLocalParam())
                reinterpret_cast<SvLocalParam*>(generic.get())
                    ->toCpp(hpp, _namespace.first, _namespace.second.aliases, noSystemC);
        }

        hpp.decreaseIndent();
        hpp.addWithIndent("}\n");
    }
}
