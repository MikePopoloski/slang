#!/usr/bin/env python
# This script generates C++ source for parse tree syntax nodes from a data file.
#
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import argparse
import math
import os


class TypeInfo:
    def __init__(
        self,
        processedMembers,
        members,
        pointerMembers,
        optionalMembers,
        final,
        constructorArgs,
        argNames,
        base,
        combinedMembers,
        notNullMembers,
        kindValue,
        initializers,
        baseInitializers,
    ):
        self.processedMembers = processedMembers
        self.members = members
        self.pointerMembers = pointerMembers
        self.optionalMembers = optionalMembers
        self.final = final
        self.constructorArgs = constructorArgs
        self.argNames = argNames
        self.base = base
        self.combinedMembers = combinedMembers
        self.notNullMembers = notNullMembers
        self.kindValue = kindValue
        self.initializers = initializers
        self.baseInitializers = baseInitializers


vowels = ("a", "e", "i", "o", "u", "A", "E", "I", "O", "U")


def main():
    parser = argparse.ArgumentParser(description="Diagnostic source generator")
    parser.add_argument("--dir", default=os.getcwd(), help="Output directory")
    parser.add_argument("--python-bindings", action="store_true")
    parser.add_argument("--syntax", help="full path to syntax file")
    args = parser.parse_args()

    inputdir = os.path.dirname(args.syntax)
    alltypes, kindmap = loadalltypes(inputdir)

    if args.python_bindings:
        generatePyBindings(args.dir, alltypes)
    else:
        generateSyntaxClone(args.dir, alltypes, kindmap)
        generateSyntax(args.dir, alltypes, kindmap)
        generateTokenKinds(inputdir, args.dir)


def loadalltypes(ourdir):
    inf = open(os.path.join(ourdir, "syntax.txt"))

    currtype = None
    currkind = None
    currtype_name = None
    tags = None
    alltypes = {}
    kindmap = {}

    alltypes["SyntaxNode"] = TypeInfo(
        None, None, None, None, "", None, None, None, [], None, "", None, None
    )

    for line in [x.strip("\n") for x in inf]:
        if line.startswith("//"):
            continue
        elif not line or (currtype is not None and line == "empty"):
            if currtype is not None:
                createtype(currtype_name, tags, currtype, alltypes, kindmap)
            currtype = None
            currkind = None
        elif currtype is not None:
            p = line.split(" ")
            if len(p) != 2:
                raise Exception("Two elements per member please.")
            currtype.append(p)
        elif currkind is not None:
            for k in line.split(" "):
                if k in kindmap:
                    raise Exception("More than one kind map for {}".format(k))
                kindmap[k] = currkind
        elif line.startswith("kindmap<"):
            currkind = line[8 : line.index(">")] + "Syntax"
        else:
            p = line.split(" ")
            currtype_name = p[0] + "Syntax"
            tags = p[1:] if len(p) > 1 else None
            currtype = []

    if currtype:
        createtype(currtype_name, tags, currtype, alltypes, kindmap)

    return (alltypes, kindmap)


def createtype(name, tags, members, alltypes, kindmap):
    tagdict = {}
    if tags:
        for t in tags:
            p = t.split("=")
            tagdict[p[0]] = p[1]

    base = tagdict["base"] + "Syntax" if "base" in tagdict else "SyntaxNode"

    pointerMembers = set()
    optionalMembers = set()
    notNullMembers = set()
    processedMembers = []
    baseInitializers = ""
    combined = members
    if base != "SyntaxNode":
        processedMembers.extend(alltypes[base].processedMembers)
        pointerMembers = pointerMembers.union(alltypes[base].pointerMembers)
        optionalMembers = optionalMembers.union(alltypes[base].optionalMembers)
        notNullMembers = notNullMembers.union(alltypes[base].notNullMembers)
        baseInitializers = ", ".join([x[1] for x in alltypes[base].members])
        if baseInitializers:
            baseInitializers = ", " + baseInitializers
        combined = alltypes[base].members + members

    for m in members:
        if m[0] == "token":
            m[0] = "Token"
            typename = m[0]
        elif m[0] == "tokenlist":
            m[0] = "TokenList"
            typename = m[0]
            pointerMembers.add(m[1])
        elif m[0].startswith("list<"):
            last = m[0][5 : m[0].index(">")]
            if not last.endswith("SyntaxNode"):
                last += "Syntax"

            m[0] = "SyntaxList<" + last + ">"
            typename = m[0]
            pointerMembers.add(m[1])
        elif m[0].startswith("separated_list<"):
            last = m[0][15 : m[0].index(">")]
            if not last.endswith("SyntaxNode"):
                last += "Syntax"

            m[0] = "SeparatedSyntaxList<" + last + ">"
            typename = m[0]
            pointerMembers.add(m[1])
        else:
            optional = False
            if m[0].endswith("?"):
                optional = True
                m[0] = m[0][:-1]

            if m[0] != "SyntaxNode":
                m[0] += "Syntax"

            if m[0] not in alltypes:
                raise Exception("Unknown type '{}'".format(m[0]))

            typename = m[0]
            if optional:
                m[0] += "*"
                optionalMembers.add(m[1])
            else:
                m[0] += "&"
                notNullMembers.add(m[1])

        m.append(typename)
        processedMembers.append("{} {}".format(m[0], m[1]))
        if m[1] in notNullMembers:
            m[0] = "not_null<{}*>".format(typename)

    final = " final"
    if "final" in tagdict and tagdict["final"] == "false":
        final = ""

    kindArg = "SyntaxKind kind"
    kindValue = "kind"
    argNames = []

    if not final or tagdict.get("multiKind") == "true":
        argNames.append("kind")
    else:
        k = name
        if k.endswith("Syntax"):
            k = k[:-6]

        if k in kindmap:
            raise Exception("More than one kind map for {}".format(k))
        kindmap[k] = name
        kindArg = ""
        kindValue = "SyntaxKind::" + k

    if kindArg and processedMembers:
        kindArg += ", "

    initializers = ", ".join(
        [
            "{0}({1}{0})".format(x[1], "&" if x[1] in notNullMembers else "")
            for x in members
        ]
    )
    if initializers:
        initializers = ", " + initializers

    argMembers = []
    for m in processedMembers:
        space = m.index(" ")
        argNames.append(m[space + 1 :])

        if (
            m.startswith("SyntaxList<")
            or m.startswith("SeparatedSyntaxList<")
            or m.startswith("TokenList")
        ):
            argMembers.append("const {}&{}".format(m[:space], m[space:]))
        else:
            argMembers.append(m)

    if final and not argMembers:
        raise Exception("{} has no members".format(name))

    constructorArgs = "{}{}".format(kindArg, ", ".join(argMembers))
    alltypes[name] = TypeInfo(
        processedMembers,
        members,
        pointerMembers,
        optionalMembers,
        final,
        constructorArgs,
        argNames,
        base,
        combined,
        notNullMembers,
        kindValue,
        initializers,
        baseInitializers,
    )


def generateSyntax(builddir, alltypes, kindmap):
    # Make sure the output directory exists.
    headerdir = os.path.join(builddir, "slang", "syntax")
    try:
        os.makedirs(headerdir)
    except OSError:
        pass

    # Start the header file.
    outf = open(os.path.join(headerdir, "AllSyntax.h"), "w")
    outf.write(
        """//------------------------------------------------------------------------------
//! @file AllSyntax.h
//! @brief All generated syntax node data structures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/util/BumpAllocator.h"

// This file contains all parse tree syntax nodes.
// It is auto-generated by the syntax_gen.py script under the scripts/ directory.

namespace slang::syntax {

"""
    )

    # Start a documentation header file.
    docf = open(os.path.join(headerdir, "SyntaxDoc.dox"), "w")
    docf.write("/** @file */\n\n")

    # Write all type definitions.
    alltypesSaved = alltypes.copy()
    for name, currtype in alltypes.items():
        if name == "SyntaxNode":
            continue

        outf.write(
            "struct SLANG_EXPORT {} : public {} {{\n".format(name, currtype.base)
        )

        article = "an" if name[0] in vowels else "a"
        docf.write("/** @struct slang::syntax::{}\n".format(name))
        docf.write(
            "    @brief Concrete syntax definition for {} {}\n".format(
                article, name[:-6]
            )
        )

        for m in currtype.members:
            outf.write("    {} {};\n".format(m[0], m[1]))
            docf.write("    @var slang::syntax::{}::{}\n".format(name, m[1]))
            docf.write("    @brief The {} member\n".format(m[1]))

        outf.write("\n")
        outf.write("    {}({}) :\n".format(name, currtype.constructorArgs))
        outf.write(
            "        {}({}{}){} {{\n".format(
                currtype.base,
                currtype.kindValue,
                currtype.baseInitializers,
                currtype.initializers,
            )
        )

        docf.write(
            "    @fn slang::syntax::{}::{}({})\n".format(
                name, name, currtype.constructorArgs
            )
        )
        docf.write(
            "    @brief Constructs a new instance of the {} struct\n".format(name)
        )

        # Write constructor body.
        for m in currtype.members:
            if m[0] == "Token":
                continue
            if m[1] in currtype.pointerMembers:
                outf.write("        this->{}.parent = this;\n".format(m[1]))
                if m[0].startswith("SyntaxList<") or m[0].startswith(
                    "SeparatedSyntaxList<"
                ):
                    outf.write("        for (auto child : this->{})\n".format(m[1]))
                    outf.write("            child->parent = this;\n")
            elif m[1] in currtype.optionalMembers:
                outf.write(
                    "        if (this->{0}) this->{0}->parent = this;\n".format(m[1])
                )
            else:
                outf.write("        this->{}->parent = this;\n".format(m[1]))

        outf.write("    }\n\n")

        # Copy constructor (defaulted).
        outf.write("    explicit {}(const {}&) = default;\n\n".format(name, name))

        docf.write(
            "    @fn slang::syntax::{}::{}(const {}&)\n".format(name, name, name)
        )
        docf.write("    @brief Copy constructor\n")

        docf.write("    @fn slang::syntax::{}::isKind\n".format(name))
        docf.write(
            "    @brief Returns true if the provided syntax kind is represented by this type\n"
        )

        if not currtype.members and currtype.final == "":
            outf.write("    static bool isKind(SyntaxKind kind);\n")
        else:
            outf.write("    static bool isKind(SyntaxKind kind);\n\n")

            outf.write("    static bool isChildOptional(size_t index);\n")
            outf.write("    TokenOrSyntax getChild(size_t index);\n")
            outf.write("    ConstTokenOrSyntax getChild(size_t index) const;\n")
            outf.write("    PtrTokenOrSyntax getChildPtr(size_t index);\n")
            outf.write("    void setChild(size_t index, TokenOrSyntax child);\n\n")

            docf.write(
                "    @fn static bool slang::syntax::{}::isChildOptional(size_t index);\n".format(
                    name
                )
            )
            docf.write(
                "    @brief Returns true if child member (token or syntax node) at the provided index within this struct is a nullable pointer\n"
            )
            docf.write(
                "    @fn TokenOrSyntax slang::syntax::{}::getChild(size_t index)\n".format(
                    name
                )
            )
            docf.write(
                "    @brief Gets the child member (token or syntax node) at the provided index within this struct\n"
            )
            docf.write(
                "    @fn ConstTokenOrSyntax slang::syntax::{}::getChild(size_t index) const\n".format(
                    name
                )
            )
            docf.write(
                "    @brief Gets the child member (token or syntax node) as a pointer at the provided index within this struct\n"
            )
            docf.write(
                "    @fn PtrTokenOrSyntax slang::syntax::{}::getChildPtr(size_t index)\n".format(
                    name
                )
            )
            docf.write(
                "    @brief Gets the child member (token or syntax node) at the provided index within this struct\n"
            )
            docf.write("    @fn slang::syntax::{}::setChild\n".format(name))
            docf.write(
                "    @brief Sets the child member (token or syntax node) at the provided index within this struct\n"
            )

        outf.write("};\n\n")
        docf.write("*/\n\n")

    # Start the source file.
    cppf = open(os.path.join(builddir, "AllSyntax.cpp"), "w")
    cppf.write(
        """//------------------------------------------------------------------------------
// AllSyntax.cpp
// All generated syntax node data structures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/AllSyntax.h"

#include <type_traits>

// This file contains all parse tree syntax node generated definitions.
// It is auto-generated by the syntax_gen.py script under the scripts/ directory.

namespace slang::syntax {

size_t SyntaxNode::getChildCount() const {
    switch (kind) {
        case SyntaxKind::Unknown: return 0;
        case SyntaxKind::SyntaxList:
        case SyntaxKind::TokenList:
        case SyntaxKind::SeparatedList:
            return ((const SyntaxListBase*)this)->getChildCount();
"""
    )

    for k, v in sorted(kindmap.items()):
        count = len(alltypes[v].combinedMembers)
        cppf.write("        case SyntaxKind::{}: return {};\n".format(k, count))

    cppf.write("    }\n")
    cppf.write("    SLANG_UNREACHABLE;\n")
    cppf.write("}\n\n")

    # Build a reverse mapping from class types to their syntax kinds.
    reverseKindmap = {}
    for k, v in kindmap.items():
        if v in reverseKindmap:
            reverseKindmap[v].append(k)
        else:
            reverseKindmap[v] = [k]

    # Continue building up the reverse map by traversing base class links.
    for k, v in alltypes.items():
        if not v.final:
            continue

        while v.base != "SyntaxNode":
            kinds = reverseKindmap[k]
            if v.base in reverseKindmap:
                reverseKindmap[v.base].extend(kinds)
            else:
                reverseKindmap[v.base] = kinds[:]
            k = v.base
            v = alltypes[k]

    # Write out isKind static methods for each derived type.
    for k, v in sorted(alltypes.items()):
        if v.base is None:
            continue

        cppf.write("bool {}::isKind(SyntaxKind kind) {{\n".format(k))
        kinds = set(reverseKindmap[k])
        if len(kinds) == 1:
            cppf.write("    return kind == SyntaxKind::{};\n".format(list(kinds)[0]))
        else:
            cppf.write("    switch (kind) {\n")
            for kind in sorted(kinds):
                cppf.write("        case SyntaxKind::{}:\n".format(kind))
            cppf.write("            return true;\n")
            cppf.write("        default:\n")
            cppf.write("            return false;\n")
            cppf.write("    }\n")

        cppf.write("}\n\n")

        if v.members or v.final != "":
            cppf.write("bool {}::isChildOptional(size_t index) {{\n".format(k))
            if v.optionalMembers:
                cppf.write("    switch (index) {\n")

                index = 0
                for m in v.combinedMembers:
                    if m[1] in v.optionalMembers:
                        cppf.write("        case {}: return true;\n".format(index))
                    index += 1

                cppf.write("        default: return false;\n")
                cppf.write("    }\n")
            else:
                cppf.write("    (void)index;\n")
                cppf.write("    return false;\n")

            cppf.write("}\n\n")

            for returnType in (
                "TokenOrSyntax",
                "ConstTokenOrSyntax",
                "PtrTokenOrSyntax",
            ):
                cppf.write(
                    "{} {}::getChild{}(size_t index){} {{\n".format(
                        returnType,
                        k,
                        ("Ptr" if returnType.startswith("Ptr") else ""),
                        "" if not returnType.startswith("Const") else " const",
                    )
                )

                returnPointer = returnType == "PtrTokenOrSyntax"

                if v.combinedMembers:
                    cppf.write("    switch (index) {\n")

                    index = 0
                    for m in v.combinedMembers:
                        addr = ""
                        if returnPointer:
                            if m[0] == "Token" or (m[1] in v.pointerMembers):
                                addr = "&"
                        elif m[1] in v.pointerMembers:
                            addr = "&"

                        # addr = "&" if  != (returnPointer and not (m[1] in v.notNullMembers)) else ""
                        get = ".get()" if m[1] in v.notNullMembers else ""
                        cppf.write(
                            "        case {}: return {}{}{};\n".format(
                                index, addr, m[1], get
                            )
                        )
                        index += 1

                    cppf.write("        default: return nullptr;\n")
                    cppf.write("    }\n")
                else:
                    cppf.write("    (void)index;\n")
                    cppf.write("    return nullptr;\n")

                cppf.write("}\n\n")

            cppf.write(
                "void {}::setChild(size_t index, TokenOrSyntax child) {{\n".format(k)
            )
            if v.combinedMembers:
                cppf.write("    switch (index) {\n")

                index = 0
                for m in v.combinedMembers:
                    cppf.write("        case {}: ".format(index))
                    index += 1

                    if m[0] == "Token":
                        cppf.write("{} = child.token(); return;\n".format(m[1]))
                    elif m[1] in v.pointerMembers:
                        cppf.write(
                            "{} = child.node()->as<{}>(); return;\n".format(m[1], m[2])
                        )
                    else:
                        cppf.write(
                            "{} = child.node() ? &child.node()->as<{}>() : nullptr; return;\n".format(
                                m[1], m[2]
                            )
                        )

                cppf.write("        default: SLANG_UNREACHABLE;\n")
                cppf.write("    }\n")
            else:
                cppf.write("    (void)index;\n")
                cppf.write("    (void)child;\n")

            cppf.write("}\n\n")

    # Write out syntax factory methods.
    outf.write("class SLANG_EXPORT SyntaxFactory {\n")
    outf.write("public:\n")
    outf.write("    using Token = parsing::Token;\n\n")
    outf.write("    explicit SyntaxFactory(BumpAllocator& alloc) : alloc(alloc) {}\n")
    outf.write("\n")

    for k, v in sorted(alltypes.items()):
        if not v.final:
            continue

        methodName = k
        if methodName.endswith("Syntax"):
            methodName = methodName[:-6]
        methodName = methodName[:1].lower() + methodName[1:]
        outf.write("    {}& {}({});\n".format(k, methodName, v.constructorArgs))

        argNames = ", ".join(v.argNames)
        cppf.write(
            "{}& SyntaxFactory::{}({}) {{\n".format(k, methodName, v.constructorArgs)
        )
        cppf.write("    return *alloc.emplace<{}>({});\n".format(k, argNames))
        cppf.write("}\n\n")

    # Write out toString methods for SyntaxKind enum.
    cppf.write(
        """
std::ostream& operator<<(std::ostream& os, SyntaxKind kind) {
    os << toString(kind);
    return os;
}

std::string_view toString(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::Unknown: return "Unknown";
        case SyntaxKind::SyntaxList: return "SyntaxList";
        case SyntaxKind::TokenList: return "TokenList";
        case SyntaxKind::SeparatedList: return "SeparatedList";
"""
    )

    for k, _ in sorted(kindmap.items()):
        cppf.write('        case SyntaxKind::{}: return "{}";\n'.format(k, k))

    cppf.write(
        """        default: return "";
    }
}

"""
    )

    # Write out traits member list for SyntaxKind enum.
    cppf.write("decltype(SyntaxKind_traits::values) SyntaxKind_traits::values = {\n")
    cppf.write(
        """    SyntaxKind::Unknown,
    SyntaxKind::SyntaxList,
    SyntaxKind::TokenList,
    SyntaxKind::SeparatedList,
"""
    )
    for k, _ in sorted(kindmap.items()):
        cppf.write("    SyntaxKind::{},\n".format(k))
    cppf.write(
        """};

#ifdef SLANG_RTTI_ENABLED
const std::type_info* typeFromSyntaxKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::Unknown: break;
        case SyntaxKind::SyntaxList:
        case SyntaxKind::TokenList:
        case SyntaxKind::SeparatedList:
            return &typeid(SyntaxNode);
"""
    )

    for k, v in sorted(kindmap.items()):
        cppf.write("        case SyntaxKind::{}: return &typeid({});\n".format(k, v))
    cppf.write(
        """    }
    return nullptr;
}
#endif

}
"""
    )

    outf.write("\n")
    outf.write("private:\n")
    outf.write("    BumpAllocator& alloc;\n")
    outf.write("};\n\n")

    # Write out a dispatch method to get from SyntaxKind to actual concrete type
    outf.write("namespace detail {\n\n")
    outf.write("struct InvalidSyntaxNode : public SyntaxNode {\n")
    outf.write(
        "    static bool isKind(SyntaxKind kind) { return kind == SyntaxKind::Unknown; }\n"
    )
    outf.write("    static bool isChildOptional(size_t) { return true; }\n")
    outf.write("    TokenOrSyntax getChild(size_t) { return nullptr; }\n")
    outf.write("    ConstTokenOrSyntax getChild(size_t) const { return nullptr; }\n")
    outf.write("    PtrTokenOrSyntax getChildPtr(size_t) { return nullptr; }\n")
    outf.write("    void setChild(size_t, TokenOrSyntax) {}\n")
    outf.write("};\n\n")

    outf.write("template<typename TNode, typename TVisitor, typename... Args>\n")
    outf.write(
        "decltype(auto) visitSyntaxNode(TNode* node, TVisitor& visitor, Args&&... args) {\n"
    )
    outf.write("    static constexpr bool isConst = std::is_const_v<TNode>;")
    outf.write("    switch (node->kind) {\n")
    outf.write(
        "        case SyntaxKind::Unknown: return visitor.visit(*static_cast<std::conditional_t<isConst, const InvalidSyntaxNode*, InvalidSyntaxNode*>>(node), std::forward<Args>(args)...);\n"
    )
    outf.write("        case SyntaxKind::SyntaxList:\n")
    outf.write("        case SyntaxKind::TokenList:\n")
    outf.write("        case SyntaxKind::SeparatedList:\n")
    outf.write(
        "            return visitor.visit(*static_cast<std::conditional_t<isConst, const SyntaxListBase*, SyntaxListBase*>>(node), std::forward<Args>(args)...);\n"
    )

    for k, v in sorted(kindmap.items()):
        outf.write(
            "        case SyntaxKind::{}: return visitor.visit(*static_cast<".format(k)
        )
        outf.write(
            "std::conditional_t<isConst, const {0}*, {0}*>>(node), std::forward<Args>(args)...);\n".format(
                v
            )
        )
        alltypes.pop(v, None)

    outf.write("    }\n")
    outf.write("    SLANG_UNREACHABLE;\n")
    outf.write("}\n\n")
    outf.write("}\n\n")

    outf.write("template<typename TVisitor, typename... Args>\n")
    outf.write(
        "decltype(auto) SyntaxNode::visit(TVisitor& visitor, Args&&... args) {\n"
    )
    outf.write(
        "    return detail::visitSyntaxNode(this, visitor, std::forward<Args>(args)...);\n"
    )
    outf.write("}\n\n")

    outf.write("template<typename TVisitor, typename... Args>\n")
    outf.write(
        "decltype(auto) SyntaxNode::visit(TVisitor& visitor, Args&&... args) const {\n"
    )
    outf.write(
        "    return detail::visitSyntaxNode(this, visitor, std::forward<Args>(args)...);\n"
    )
    outf.write("}\n\n")

    outf.write("}\n")

    # Do some checking to make sure all types have at least one kind assigned,
    # or has set final=false.  We already removed types from alltypes in the
    # loop above.
    for k, v in alltypes.items():
        if v.final:
            print("Type '{}' has no kinds assigned to it.".format(k))

    # Write out the SyntaxKind header file.
    outf = open(os.path.join(headerdir, "SyntaxKind.h"), "w")
    outf.write(
        """//------------------------------------------------------------------------------
//! @file SyntaxKind.h
//! @brief Generated SyntaxKind enum
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <ostream>
#include "slang/slang_export.h"

namespace std { class type_info; }

namespace slang::syntax {

enum class SLANG_EXPORT SyntaxKind {
    Unknown,
    SyntaxList,
    TokenList,
    SeparatedList,
"""
    )

    for k, _ in sorted(kindmap.items()):
        outf.write("    {},\n".format(k))

    outf.write(
        """}};

SLANG_EXPORT std::ostream& operator<<(std::ostream& os, SyntaxKind kind);
SLANG_EXPORT std::string_view toString(SyntaxKind kind);

class SLANG_EXPORT SyntaxKind_traits {{
public:
    static const std::array<SyntaxKind, {}> values;
}};

SLANG_EXPORT const std::type_info* typeFromSyntaxKind(SyntaxKind kind);

}}
""".format(
            len(kindmap.items()) + 4
        )
    )

    # Write the forward declaration header file.
    outf = open(os.path.join(headerdir, "SyntaxFwd.h"), "w")
    outf.write(
        """//------------------------------------------------------------------------------
//! @file SyntaxFwd.h
//! @brief Forward declarations for syntax node types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

namespace slang::syntax {

class SyntaxNode;
"""
    )

    # Write all type names.
    for name, _ in alltypesSaved.items():
        if name == "SyntaxNode":
            continue

        outf.write("struct {};\n".format(name))
    outf.write("\n}\n")


def generateSyntaxClone(builddir, alltypes, kindmap):
    # Start the clone source file.
    clonef = open(os.path.join(builddir, "SyntaxClone.cpp"), "w")
    clonef.write(
        """//------------------------------------------------------------------------------
// SyntaxClone.cpp
// All generated syntax node clone functionality
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/AllSyntax.h"

// This file contains all syntax generated clone implementations.
// It is auto-generated by the syntax_gen.py script under the scripts/ directory.

namespace slang::syntax::shallow {

template<typename T>
SyntaxNode* clone(const T& node, BumpAllocator& alloc) {
    return alloc.emplace<T>(node);
}

}

"""
    )
    clonef.write(
        """namespace slang::syntax::deep {

template<typename T>
SyntaxNode* clone(const T& node, BumpAllocator& alloc) {
    return alloc.emplace<T>(node);
}

SyntaxNode* clone(const SyntaxListBase&, BumpAllocator&) {
    return nullptr;
}

"""
    )
    # Write out deepClone methods for each derived type.
    for k, v in sorted(alltypes.items()):
        if not v.final:
            continue
        if v.final:
            clonef.write(
                "static SyntaxNode* clone(const {0}& node, BumpAllocator& alloc) {{\n".format(
                    k
                )
            )
            clonef.write("    return alloc.emplace<{0}>(\n".format(k))
            if "kind" in v.argNames:
                clonef.write("        node.kind,\n")
            for i, m in enumerate(v.combinedMembers):
                if m[1] in v.notNullMembers:
                    clonef.write(
                        "        *deepClone<{0}>(*node.{1}, alloc)".format(
                            m[0][9:-2], m[1]
                        )
                    )
                elif m[1] in v.optionalMembers:
                    clonef.write(
                        "        node.{0} ? deepClone(*node.{0}, alloc) : nullptr".format(
                            m[1]
                        )
                    )
                elif (
                    m[0].startswith("SyntaxList")
                    or m[0].startswith("SeparatedSyntaxList")
                    or m[0].startswith("TokenList")
                ):
                    clonef.write("        *deepClone(node.{0}, alloc)".format(m[1]))
                elif m[0] == "Token":
                    clonef.write("        node.{0}.deepClone(alloc)".format(m[1]))
                else:
                    clonef.write("        node.{0}".format(m[1]))
                if i != len(v.combinedMembers) - 1:
                    clonef.write(",\n")
                else:
                    clonef.write("\n")
            clonef.write("    );\n")
            clonef.write("}\n\n")
    clonef.write("}\n\n")
    clonef.write(
        """namespace slang::syntax {

struct CloneVisitor {
    template<typename T>
    SyntaxNode* visit(const T& node, BumpAllocator& alloc) {
        if constexpr (requires { node.clone(alloc); }) {
            return node.clone(alloc);
        } else {
            return shallow::clone(node, alloc);
        }
    }
};

struct DeepCloneVisitor {
    template<typename T>
    SyntaxNode* visit(const T& node, BumpAllocator& alloc) {
        return deep::clone(node, alloc);
    }
};

SyntaxNode* deepClone(const SyntaxNode& node, BumpAllocator& alloc) {
    DeepCloneVisitor visitor;
    return node.visit(visitor, alloc);
}

SyntaxNode* clone(const SyntaxNode& node, BumpAllocator& alloc) {
    CloneVisitor visitor;
    return node.visit(visitor, alloc);
}

}
"""
    )


def loadkinds(ourdir, filename):
    kinds = []
    inf = open(os.path.join(ourdir, filename))
    for line in [x.strip("\n") for x in inf]:
        line = line.strip()
        if not line:
            continue

        kinds.append(line)
    return kinds


def writekinddecl(outf, name, basetype, kinds):
    outf.write("enum class SLANG_EXPORT {} : {} {{\n".format(name, basetype))
    for k in kinds:
        outf.write("    {},\n".format(k))

    outf.write(
        """}};

SLANG_EXPORT std::ostream& operator<<(std::ostream& os, {} kind);
SLANG_EXPORT std::string_view toString({} kind);

class SLANG_EXPORT {}_traits {{
public:
    static const std::array<{}, {}> values;
}};

""".format(
            name, name, name, name, len(kinds)
        )
    )


def writekindimpls(outf, name, kinds):
    outf.write(
        """std::ostream& operator<<(std::ostream& os, {} kind) {{
    os << toString(kind);
    return os;
}}

std::string_view toString({} kind) {{
    switch (kind) {{
""".format(
            name, name
        )
    )

    for k in kinds:
        outf.write('        case {}::{}: return "{}";\n'.format(name, k, k))
    outf.write(
        """        default: return "";
    }
}

"""
    )

    outf.write(
        """decltype({}_traits::values) {}_traits::values = {{
""".format(
            name, name
        )
    )

    for k in kinds:
        outf.write("    {}::{},\n".format(name, k))
    outf.write(
        """};

"""
    )


def generateTokenKinds(ourdir, builddir):
    headerdir = os.path.join(builddir, "slang", "parsing")
    try:
        os.makedirs(headerdir)
    except OSError:
        pass

    triviakinds = loadkinds(ourdir, "triviakinds.txt")
    tokenkinds = loadkinds(ourdir, "tokenkinds.txt")

    outf = open(os.path.join(headerdir, "TokenKind.h"), "w")
    outf.write(
        """//------------------------------------------------------------------------------
//! @file TokenKind.h
//! @brief Generated TokenKind and TriviaKind enums
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <array>
#include <ostream>

#include "slang/util/Util.h"

namespace slang::parsing {

"""
    )

    writekinddecl(outf, "TriviaKind", "uint8_t", triviakinds)
    writekinddecl(outf, "TokenKind", "uint16_t", tokenkinds)
    outf.write("}\n")

    outf = open(os.path.join(builddir, "TokenKind.cpp"), "w")
    outf.write(
        """//------------------------------------------------------------------------------
// TokenKind.cpp
// Generated TokenKind and TriviaKind enums
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/TokenKind.h"

namespace slang::parsing {

"""
    )

    writekindimpls(outf, "TriviaKind", triviakinds)
    writekindimpls(outf, "TokenKind", tokenkinds)
    outf.write("}\n")


def generatePyBindings(builddir, alltypes):
    numfiles = 4
    items = list(alltypes.items())
    perfile = math.ceil(len(items) / numfiles)

    for i in range(numfiles):
        outf = open(os.path.join(builddir, f"PySyntaxBindings{i}.cpp"), "w")
        outf.write(
            """//------------------------------------------------------------------------------
// PySyntaxBindings{0}.cpp
// Generated Python bindings for syntax types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/syntax/AllSyntax.h"

void registerSyntaxNodes{0}(py::module_& m) {{
""".format(
                i
            )
        )

        idx = i * perfile
        for k, v in items[idx : idx + perfile]:
            if k == "SyntaxNode":
                continue

            outf.write('    py::class_<{}, {}>(m, "{}")'.format(k, v.base, k))
            for m in v.members:
                outf.write(
                    '\n        .def_readwrite("{}", &{}::{})'.format(m[1], k, m[1])
                )
            outf.write(";\n\n")

        outf.write("}\n")


if __name__ == "__main__":
    main()
