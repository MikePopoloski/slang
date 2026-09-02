#!/usr/bin/env python
# This script generates C++ source for parse tree syntax nodes from a data file.
#
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import argparse
import math
import os
from io import StringIO

# member tuple indices for combinedMembers entries: (type, name, base_type)
# - MEMBER_TYPE: the C++ type (e.g. "Token", "SyntaxList<...>" etc.)
# - MEMBER_NAME: the member variable's name
# - MEMBER_BASE_TYPE: for pointer/optional members, the underlying type (only present for some)
MEMBER_TYPE, MEMBER_NAME, MEMBER_BASE_TYPE = 0, 1, 2


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
        generatePyFactoryBindings(args.dir, alltypes)
    else:
        generateSyntaxClone(args.dir, alltypes, kindmap)
        # generateSyntax modifies alltypes
        generateSyntax(args.dir, alltypes.copy(), kindmap)
        generateTokenKinds(inputdir, args.dir)
        generateSystemNames(inputdir, args.dir)
        generateCSTJson(args.dir, alltypes)


def loadalltypes(ourdir):
    with open(os.path.join(ourdir, "syntax.txt")) as f:
        inf = f.readlines()

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
                raise ValueError("Two elements per member please.")
            currtype.append(p)
        elif currkind is not None:
            for k in line.split(" "):
                if k in kindmap:
                    raise ValueError(f"More than one kind map for {k}")
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
                raise ValueError(f"Unknown type '{m[0]}'")

            typename = m[0]
            if optional:
                m[0] += "*"
                optionalMembers.add(m[1])
            else:
                m[0] += "&"
                notNullMembers.add(m[1])

        m.append(typename)
        processedMembers.append(f"{m[0]} {m[1]}")
        if m[1] in notNullMembers:
            m[0] = f"not_null<{typename}*>"

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
        k = k.removesuffix("Syntax")

        if k in kindmap:
            raise ValueError(f"More than one kind map for {k}")
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

        if m.startswith(("SyntaxList<", "SeparatedSyntaxList<", "TokenList")):
            argMembers.append(f"const {m[:space]}&{m[space:]}")
        else:
            argMembers.append(m)

    if final and not argMembers:
        raise ValueError(f"{name} has no members")

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
    headerdir = os.path.join(builddir, "slang", "syntax")
    try:
        os.makedirs(headerdir)
    except OSError:
        pass

    # Start the header file.
    outf = StringIO()
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
    docf = StringIO()
    docf.write("/** @file */\n\n")

    # Write all type definitions.
    alltypesSaved = alltypes.copy()
    for name, currtype in alltypes.items():
        if name == "SyntaxNode":
            continue

        outf.write(f"struct SLANG_EXPORT {name} : public {currtype.base} {{\n")

        article = "an" if name[0] in vowels else "a"
        docf.write(f"/** @struct slang::syntax::{name}\n")
        docf.write(f"    @brief Concrete syntax definition for {article} {name[:-6]}\n")

        for m in currtype.members:
            outf.write(f"    {m[0]} {m[1]};\n")
            docf.write(f"    @var slang::syntax::{name}::{m[1]}\n")
            docf.write(f"    @brief The {m[1]} member\n")

        outf.write("\n")
        outf.write(f"    {name}({currtype.constructorArgs}) :\n")
        outf.write(
            f"        {currtype.base}({currtype.kindValue}{currtype.baseInitializers}){currtype.initializers} {{\n"
        )

        docf.write(
            f"    @fn slang::syntax::{name}::{name}({currtype.constructorArgs})\n"
        )
        docf.write(f"    @brief Constructs a new instance of the {name} struct\n")

        # Write constructor body.
        for m in currtype.members:
            if m[0] == "Token":
                continue
            if m[1] in currtype.pointerMembers:
                if m[0].startswith("SyntaxList<") or m[0].startswith(
                    "SeparatedSyntaxList<"
                ):
                    # Lists are standalone (not derived from SyntaxNode); they
                    # have no parent pointer of their own. Their elements still
                    # parent to the enclosing real node.
                    outf.write(f"        for (auto child : this->{m[1]})\n")
                    outf.write("            child->parent = this;\n")
                elif m[0] == "TokenList":
                    # TokenList holds Tokens which have no parent pointer; nothing
                    # to wire up.
                    pass
                else:
                    outf.write(f"        this->{m[1]}.parent = this;\n")
            elif m[1] in currtype.optionalMembers:
                outf.write(
                    "        if (this->{0}) this->{0}->parent = this;\n".format(m[1])
                )
            else:
                outf.write(f"        this->{m[1]}->parent = this;\n")

        outf.write("    }\n\n")

        # Copy constructor (defaulted).
        outf.write(f"    explicit {name}(const {name}&) = default;\n\n")

        docf.write(f"    @fn slang::syntax::{name}::{name}(const {name}&)\n")
        docf.write("    @brief Copy constructor\n")

        docf.write(f"    @fn slang::syntax::{name}::isKind\n")
        docf.write(
            "    @brief Returns true if the provided syntax kind is represented by this type\n"
        )

        if not currtype.members and currtype.final == "":
            outf.write("    static bool isKind(SyntaxKind kind);\n")
        else:
            outf.write("    static bool isKind(SyntaxKind kind);\n\n")

            outf.write("    bool isChildOptional(size_t index) const;\n")
            outf.write("    TokenOrSyntax getChild(size_t index);\n")
            outf.write("    ConstTokenOrSyntax getChild(size_t index) const;\n")
            outf.write("    PtrTokenOrSyntax getChildPtr(size_t index);\n")
            outf.write("    void setChild(size_t index, TokenOrSyntax child);\n\n")

            docf.write(
                f"    @fn static bool slang::syntax::{name}::isChildOptional(size_t index);\n"
            )
            docf.write(
                "    @brief Returns true if child member (token or syntax node) at the provided index within this struct is a nullable pointer\n"
            )
            docf.write(
                f"    @fn TokenOrSyntax slang::syntax::{name}::getChild(size_t index)\n"
            )
            docf.write(
                "    @brief Gets the child member (token or syntax node) at the provided index within this struct\n"
            )
            docf.write(
                f"    @fn ConstTokenOrSyntax slang::syntax::{name}::getChild(size_t index) const\n"
            )
            docf.write(
                "    @brief Gets the child member (token or syntax node) as a pointer at the provided index within this struct\n"
            )
            docf.write(
                f"    @fn PtrTokenOrSyntax slang::syntax::{name}::getChildPtr(size_t index)\n"
            )
            docf.write(
                "    @brief Gets the child member (token or syntax node) at the provided index within this struct\n"
            )
            docf.write(f"    @fn slang::syntax::{name}::setChild\n")
            docf.write(
                "    @brief Sets the child member (token or syntax node) at the provided index within this struct\n"
            )

        outf.write("};\n\n")
        docf.write("*/\n\n")

    # Start the source file.
    cppf = StringIO()
    cppf.write(
        """//------------------------------------------------------------------------------
// AllSyntax.cpp
// All generated syntax node data structures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxListInfo.h"

#include <type_traits>

// This file contains all parse tree syntax node generated definitions.
// It is auto-generated by the syntax_gen.py script under the scripts/ directory.

namespace slang::syntax {

size_t SyntaxNode::getChildCount() const {
    switch (kind) {
        case SyntaxKind::Unknown: return 0;
"""
    )

    for k, v in sorted(kindmap.items()):
        ti = alltypes[v]
        # Build an expression for the flattened child count. Non-list members
        # contribute 1; list members contribute their dynamic getChildCount().
        const_count = 0
        list_terms = []
        for m in ti.combinedMembers:
            if (
                m[0].startswith("SyntaxList<")
                or m[0].startswith("SeparatedSyntaxList<")
                or m[0].startswith("TokenList")
            ):
                list_terms.append(f"((const {v}*)this)->{m[1]}.getChildCount()")
            else:
                const_count += 1
        if not list_terms:
            cppf.write(f"        case SyntaxKind::{k}: return {const_count};\n")
        else:
            expr = (
                " + ".join([str(const_count)] + list_terms)
                if const_count
                else " + ".join(list_terms)
            )
            cppf.write(f"        case SyntaxKind::{k}: return {expr};\n")

    cppf.write("    }\n")
    cppf.write("    SLANG_UNREACHABLE;\n")
    cppf.write("}\n\n")

    cppf.write(
        "void getChildListInfo(SyntaxNode& node,\n"
        "                      SmallVector<ListChildInfo, 2>& out) {\n"
        "    switch (node.kind) {\n"
    )
    for k, v in sorted(kindmap.items()):
        ti = alltypes[v]
        list_members = [
            m
            for m in ti.combinedMembers
            if m[0].startswith("SyntaxList<")
            or m[0].startswith("SeparatedSyntaxList<")
            or m[0].startswith("TokenList")
        ]
        if not list_members:
            continue

        def is_list(mtype):
            return (
                mtype.startswith(("SyntaxList<", "SeparatedSyntaxList<"))
                or mtype == "TokenList"
            )

        # Find index of last list member; we don't need to advance flatStart past it.
        last_list_idx = max(
            i for i, m in enumerate(ti.combinedMembers) if is_list(m[0])
        )

        cppf.write(f"        case SyntaxKind::{k}: {{\n")
        cppf.write(f"            auto& self = static_cast<{v}&>(node);\n")
        cppf.write("            size_t flatStart = 0;\n")
        for i, m in enumerate(ti.combinedMembers[: last_list_idx + 1]):
            mtype, mname = m[0], m[1]
            if is_list(mtype):
                cppf.write(f"            out.push_back({{self.{mname}, flatStart}});\n")
                if i != last_list_idx:
                    cppf.write(
                        f"            flatStart += self.{mname}.getChildCount();\n"
                    )
            else:
                cppf.write("            ++flatStart;\n")
        cppf.write("            return;\n")
        cppf.write("        }\n")
    cppf.write("        default: return;\n")
    cppf.write("    }\n")
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

        cppf.write(f"bool {k}::isKind(SyntaxKind kind) {{\n")
        kinds = set(reverseKindmap[k])
        if len(kinds) == 1:
            cppf.write(f"    return kind == SyntaxKind::{next(iter(kinds))};\n")
        else:
            cppf.write("    switch (kind) {\n")
            cppf.writelines(
                f"        case SyntaxKind::{kind}:\n" for kind in sorted(kinds)
            )
            cppf.write("            return true;\n")
            cppf.write("        default:\n")
            cppf.write("            return false;\n")
            cppf.write("    }\n")

        cppf.write("}\n\n")

        if v.members or v.final != "":
            # Determine whether this type has any list-typed members. If so, the
            # child index space exposed by getChild()/setChild()/isChildOptional()
            # is "flattened": list members contribute multiple slots (one per
            # element) instead of a single slot.
            def is_list_member(m):
                return (
                    m[0].startswith("SyntaxList<")
                    or m[0].startswith("SeparatedSyntaxList<")
                    or m[0].startswith("TokenList")
                )

            has_list = any(is_list_member(m) for m in v.combinedMembers)

            cppf.write(f"bool {k}::isChildOptional(size_t index) const {{\n")
            if not has_list:
                if v.optionalMembers:
                    cppf.write("    switch (index) {\n")
                    for idx, m in enumerate(v.combinedMembers):
                        if m[1] in v.optionalMembers:
                            cppf.write(f"        case {idx}: return true;\n")
                    cppf.write("        default: return false;\n")
                    cppf.write("    }\n")
                else:
                    cppf.write("    (void)index;\n")
                    cppf.write("    return false;\n")
            else:
                # Walk members; for non-list members emit a single index check
                # and decrement; for list members consume `size` slots and skip.
                # Within a list, individual element slots are reported as
                # optional (matches the legacy SyntaxListBase behavior).
                last_idx = len(v.combinedMembers) - 1
                for i, m in enumerate(v.combinedMembers):
                    is_last = i == last_idx
                    if is_list_member(m):
                        cppf.write(
                            f"    if (index < {m[1]}.getChildCount()) return true;\n"
                        )
                        if not is_last:
                            cppf.write(f"    index -= {m[1]}.getChildCount();\n")
                    else:
                        if m[1] in v.optionalMembers:
                            cppf.write("    if (index == 0) return true;\n")
                        else:
                            cppf.write("    if (index == 0) return false;\n")
                        if not is_last:
                            cppf.write("    --index;\n")
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

                if not v.combinedMembers:
                    cppf.write("    (void)index;\n")
                    cppf.write("    return nullptr;\n")
                elif not has_list:
                    cppf.write("    switch (index) {\n")
                    for idx, m in enumerate(v.combinedMembers):
                        addr = ""
                        if returnPointer:
                            if m[0] == "Token" or (m[1] in v.pointerMembers):
                                addr = "&"
                        elif m[1] in v.pointerMembers:
                            addr = "&"
                        get = ".get()" if m[1] in v.notNullMembers else ""
                        cppf.write(f"        case {idx}: return {addr}{m[1]}{get};\n")
                    cppf.write("        default: return nullptr;\n")
                    cppf.write("    }\n")
                else:
                    last_idx = len(v.combinedMembers) - 1
                    for i, m in enumerate(v.combinedMembers):
                        is_last = i == last_idx
                        if is_list_member(m):
                            method = "getChildPtr" if returnPointer else "getChild"
                            cppf.write(
                                "    if (index < {0}.getChildCount()) return {0}.{1}(index);\n".format(
                                    m[1], method
                                )
                            )
                            if not is_last:
                                cppf.write(f"    index -= {m[1]}.getChildCount();\n")
                        else:
                            addr = ""
                            if returnPointer:
                                if m[0] == "Token" or (m[1] in v.pointerMembers):
                                    addr = "&"
                            elif m[1] in v.pointerMembers:
                                addr = "&"
                            get = ".get()" if m[1] in v.notNullMembers else ""
                            cppf.write(
                                f"    if (index == 0) return {addr}{m[1]}{get};\n"
                            )
                            if not is_last:
                                cppf.write("    --index;\n")
                    cppf.write("    return nullptr;\n")

                cppf.write("}\n\n")

            cppf.write(f"void {k}::setChild(size_t index, TokenOrSyntax child) {{\n")
            if not v.combinedMembers:
                cppf.write("    (void)index;\n")
                cppf.write("    (void)child;\n")
            elif not has_list:
                cppf.write("    switch (index) {\n")
                for idx, m in enumerate(v.combinedMembers):
                    cppf.write(f"        case {idx}: ")
                    if m[0] == "Token":
                        cppf.write(f"{m[1]} = child.token(); return;\n")
                    elif m[1] in v.pointerMembers:
                        cppf.write(f"{m[1]} = child.node()->as<{m[2]}>(); return;\n")
                    else:
                        cppf.write(
                            f"{m[1]} = child.node() ? &child.node()->as<{m[2]}>() : nullptr; return;\n"
                        )
                cppf.write("        default: SLANG_UNREACHABLE;\n")
                cppf.write("    }\n")
            else:
                last_idx = len(v.combinedMembers) - 1
                for i, m in enumerate(v.combinedMembers):
                    is_last = i == last_idx
                    if is_list_member(m):
                        cppf.write(
                            "    if (index < {0}.getChildCount()) {{ {0}.setChild(index, child); return; }}\n".format(
                                m[1]
                            )
                        )
                        if not is_last:
                            cppf.write(f"    index -= {m[1]}.getChildCount();\n")
                    elif m[0] == "Token":
                        cppf.write(
                            f"    if (index == 0) {{ {m[1]} = child.token(); return; }}\n"
                        )
                        if not is_last:
                            cppf.write("    --index;\n")
                    elif m[1] in v.pointerMembers:
                        cppf.write(
                            f"    if (index == 0) {{ {m[1]} = child.node()->as<{m[2]}>(); return; }}\n"
                        )
                        if not is_last:
                            cppf.write("    --index;\n")
                    else:
                        cppf.write(
                            f"    if (index == 0) {{ {m[1]} = child.node() ? &child.node()->as<{m[2]}>() : nullptr; return; }}\n"
                        )
                        if not is_last:
                            cppf.write("    --index;\n")
                cppf.write("    SLANG_UNREACHABLE;\n")
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
        methodName = methodName.removesuffix("Syntax")
        methodName = methodName[:1].lower() + methodName[1:]
        outf.write(f"    {k}& {methodName}({v.constructorArgs});\n")

        argNames = ", ".join(v.argNames)
        cppf.write(f"{k}& SyntaxFactory::{methodName}({v.constructorArgs}) {{\n")
        cppf.write(f"    return *alloc.emplace<{k}>({argNames});\n")
        cppf.write("}\n\n")

    # Write out toString methods for SyntaxKind enum.
    cppf.write("""
std::ostream& operator<<(std::ostream& os, SyntaxKind kind) {
    os << toString(kind);
    return os;
}

std::string_view toString(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::Unknown: return "Unknown";
""")

    for k, _ in sorted(kindmap.items()):
        cppf.write(f'        case SyntaxKind::{k}: return "{k}";\n')

    cppf.write("""    }
    return "";
}

""")

    # Write out traits member list for SyntaxKind enum.
    cppf.write("decltype(SyntaxKind_traits::values) SyntaxKind_traits::values = {\n")
    cppf.write("""    SyntaxKind::Unknown,
""")
    for k, _ in sorted(kindmap.items()):
        cppf.write(f"    SyntaxKind::{k},\n")
    cppf.write("""};

#ifdef SLANG_RTTI_ENABLED
const std::type_info* typeFromSyntaxKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::Unknown: break;
""")

    for k, v in sorted(kindmap.items()):
        cppf.write(f"        case SyntaxKind::{k}: return &typeid({v});\n")
    cppf.write("""    }
    return nullptr;
}
#endif

}
""")

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
        "decltype(auto) visitSyntaxNode(TNode* node, TVisitor&& visitor, Args&&... args) {\n"
    )
    outf.write("    static constexpr bool isConst = std::is_const_v<TNode>;")
    outf.write("    switch (node->kind) {\n")
    outf.write(
        "        case SyntaxKind::Unknown: return visitor.visit(*static_cast<std::conditional_t<isConst, const InvalidSyntaxNode*, InvalidSyntaxNode*>>(node), std::forward<Args>(args)...);\n"
    )

    for k, v in sorted(kindmap.items()):
        outf.write(f"        case SyntaxKind::{k}: return visitor.visit(*static_cast<")
        outf.write(
            f"std::conditional_t<isConst, const {v}*, {v}*>>(node), std::forward<Args>(args)...);\n"
        )
        alltypes.pop(v, None)

    outf.write("    }\n")
    outf.write("    SLANG_UNREACHABLE;\n")
    outf.write("}\n\n")
    outf.write("}\n\n")

    outf.write("template<typename TVisitor, typename... Args>\n")
    outf.write(
        "decltype(auto) SyntaxNode::visit(TVisitor&& visitor, Args&&... args) {\n"
    )
    outf.write(
        "    return detail::visitSyntaxNode(this, visitor, std::forward<Args>(args)...);\n"
    )
    outf.write("}\n\n")

    outf.write("template<typename TVisitor, typename... Args>\n")
    outf.write(
        "decltype(auto) SyntaxNode::visit(TVisitor&& visitor, Args&&... args) const {\n"
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
            print(f"Type '{k}' has no kinds assigned to it.")

    with open(os.path.join(headerdir, "AllSyntax.h"), "w") as f:
        f.write(outf.getvalue())
    with open(os.path.join(headerdir, "SyntaxDoc.dox"), "w") as f:
        f.write(docf.getvalue())
    with open(os.path.join(builddir, "AllSyntax.cpp"), "w") as f:
        f.write(cppf.getvalue())

    # Write out the SyntaxKind header file.
    outf = StringIO()
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
"""
    )

    for k, _ in sorted(kindmap.items()):
        outf.write(f"    {k},\n")

    outf.write(
        f"""}};

SLANG_EXPORT std::ostream& operator<<(std::ostream& os, SyntaxKind kind);
SLANG_EXPORT std::string_view toString(SyntaxKind kind);

class SLANG_EXPORT SyntaxKind_traits {{
public:
    static const std::array<SyntaxKind, {len(kindmap.items()) + 1}> values;
}};

SLANG_EXPORT const std::type_info* typeFromSyntaxKind(SyntaxKind kind);

}}
"""
    )

    with open(os.path.join(headerdir, "SyntaxKind.h"), "w") as f:
        f.write(outf.getvalue())

    # Write the forward declaration header file.
    outf = StringIO()
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
    for name in alltypesSaved:
        if name == "SyntaxNode":
            continue

        outf.write(f"struct {name};\n")
    outf.write("\n}\n")

    with open(os.path.join(headerdir, "SyntaxFwd.h"), "w") as f:
        f.write(outf.getvalue())


def generateSyntaxClone(builddir, alltypes, kindmap):
    # Start the clone source file.
    clonef = StringIO()
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
    clonef.write("""namespace slang::syntax::deep {

template<typename T>
SyntaxNode* clone(const T& node, BumpAllocator& alloc) {
    return alloc.emplace<T>(node);
}

""")
    # Write out deepClone methods for each derived type.
    for k, v in sorted(alltypes.items()):
        if not v.final:
            continue
        if v.final:
            clonef.write(
                f"static SyntaxNode* clone(const {k}& node, BumpAllocator& alloc) {{\n"
            )
            clonef.write(f"    return alloc.emplace<{k}>(\n")
            if "kind" in v.argNames:
                clonef.write("        node.kind,\n")
            for i, m in enumerate(v.combinedMembers):
                if m[1] in v.notNullMembers:
                    clonef.write(
                        f"        *deepClone<{m[0][9:-2]}>(*node.{m[1]}, alloc)"
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
                    clonef.write(f"        *deepClone(node.{m[1]}, alloc)")
                elif m[0] == "Token":
                    clonef.write(f"        node.{m[1]}.deepClone(alloc)")
                else:
                    clonef.write(f"        node.{m[1]}")
                if i != len(v.combinedMembers) - 1:
                    clonef.write(",\n")
                else:
                    clonef.write("\n")
            clonef.write("    );\n")
            clonef.write("}\n\n")
    clonef.write("}\n\n")
    clonef.write("""namespace slang::syntax {

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
""")

    with open(os.path.join(builddir, "SyntaxClone.cpp"), "w") as f:
        f.write(clonef.getvalue())


def loadkinds(ourdir, filename):
    kinds = []
    with open(os.path.join(ourdir, filename)) as f:
        inf = f.readlines()
    for line in [x.strip("\n") for x in inf]:
        line = line.strip()
        if not line:
            continue

        kinds.append(line)
    return kinds


def writekinddecl(outf, name, basetype, kinds):
    outf.write(f"enum class SLANG_EXPORT {name} : {basetype} {{\n")
    for k in kinds:
        outf.write(f"    {k},\n")

    outf.write(
        f"""}};

SLANG_EXPORT std::ostream& operator<<(std::ostream& os, {name} kind);
SLANG_EXPORT std::string_view toString({name} kind);

class SLANG_EXPORT {name}_traits {{
public:
    static const std::array<{name}, {len(kinds)}> values;
}};

"""
    )


def writekindimpls(outf, name, kinds):
    outf.write(
        f"""std::ostream& operator<<(std::ostream& os, {name} kind) {{
    os << toString(kind);
    return os;
}}

std::string_view toString({name} kind) {{
    switch (kind) {{
"""
    )

    for k in kinds:
        outf.write(f'        case {name}::{k}: return "{k}";\n')
    outf.write("""    }
    return "";
}

""")

    outf.write(
        f"""decltype({name}_traits::values) {name}_traits::values = {{
"""
    )

    for k in kinds:
        outf.write(f"    {name}::{k},\n")
    outf.write("""};

""")


def generateTokenKinds(ourdir, builddir):
    headerdir = os.path.join(builddir, "slang", "parsing")
    try:
        os.makedirs(headerdir)
    except OSError:
        pass

    triviakinds = loadkinds(ourdir, "triviakinds.txt")
    tokenkinds = loadkinds(ourdir, "tokenkinds.txt")

    outf = StringIO()
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

    with open(os.path.join(headerdir, "TokenKind.h"), "w") as f:
        f.write(outf.getvalue())

    outf = StringIO()
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

    with open(os.path.join(builddir, "TokenKind.cpp"), "w") as f:
        f.write(outf.getvalue())


def generateSystemNames(ourdir, builddir):
    headerdir = os.path.join(builddir, "slang", "parsing")
    try:
        os.makedirs(headerdir)
    except OSError:
        pass

    names = []
    with open(os.path.join(ourdir, "systemnames.txt")) as f:
        inf = f.readlines()
    for line in [x.strip("\n") for x in inf]:
        line = line.strip()
        if not line:
            continue

        names.append(line.split())

    outf = StringIO()
    outf.write(
        """//------------------------------------------------------------------------------
//! @file KnownSystemName.h
//! @brief Generated KnownSystemName enum
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <array>
#include <ostream>

#include "slang/util/Util.h"

namespace slang::parsing {

enum class SLANG_EXPORT KnownSystemName {
    Unknown,
"""
    )

    outf.writelines(f"    {name[1]},\n" for name in names)

    outf.write(
        f"""}};

SLANG_EXPORT std::ostream& operator<<(std::ostream& os, KnownSystemName ksn);
SLANG_EXPORT std::string_view toString(KnownSystemName ksn);
SLANG_EXPORT KnownSystemName parseKnownSystemName(std::string_view str);

class SLANG_EXPORT KnownSystemName_traits {{
public:
    static const std::array<KnownSystemName, {len(names) + 1}> values;
}};

}}
"""
    )

    with open(os.path.join(headerdir, "KnownSystemName.h"), "w") as f:
        f.write(outf.getvalue())

    outf = StringIO()
    outf.write(
        """//------------------------------------------------------------------------------
// KnownSystemName.cpp
// Generated KnownSystemName enum
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/KnownSystemName.h"

#include "slang/util/FlatMap.h"

namespace slang::parsing {

std::ostream& operator<<(std::ostream& os, KnownSystemName ksn) {
    os << toString(ksn);
    return os;
}

std::string_view toString(KnownSystemName ksn) {
    switch (ksn) {
        case KnownSystemName::Unknown: return "Unknown";
"""
    )

    outf.writelines(
        f'        case KnownSystemName::{name[1]}: return "{name[0]}";\n'
        for name in names
    )

    outf.write("""    }
    return "";
}

const static flat_hash_map<std::string_view, KnownSystemName> ksnTable = {
""")

    outf.writelines(
        f'    {{ "{name[0]}", KnownSystemName::{name[1]} }},\n' for name in names
    )

    outf.write("""};

KnownSystemName parseKnownSystemName(std::string_view str) {
    if (auto it = ksnTable.find(str); it != ksnTable.end())
        return it->second;
    return KnownSystemName::Unknown;
}

decltype(KnownSystemName_traits::values) KnownSystemName_traits::values = {
    KnownSystemName::Unknown,
""")

    outf.writelines(f"    KnownSystemName::{name[1]},\n" for name in names)

    outf.write("""};

}
""")

    with open(os.path.join(builddir, "KnownSystemName.cpp"), "w") as f:
        f.write(outf.getvalue())


def generatePyBindings(builddir, alltypes):
    numfiles = 4
    items = list(alltypes.items())
    perfile = math.ceil(len(items) / numfiles)

    for i in range(numfiles):
        outf = StringIO()
        outf.write(
            f"""//------------------------------------------------------------------------------
// PySyntaxBindings{i}.cpp
// Generated Python bindings for syntax types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/syntax/AllSyntax.h"

void registerSyntaxNodes{i}(nb::module_& m) {{
"""
        )

        idx = i * perfile
        for class_name, v in items[idx : idx + perfile]:
            if class_name == "SyntaxNode":
                continue

            outf.write(f'    nb::class_<{class_name}, {v.base}>(m, "{class_name}")')
            for member_name in v.members:
                python_member_name = member_name[1]

                # Validate and rewrite invalid Python attribute names.
                if python_member_name == "with":
                    python_member_name = "with_"

                outf.write(
                    f'\n        .def_rw("{python_member_name}",'
                    f" &{class_name}::{member_name[1]})"
                )
            outf.write(";\n\n")

        outf.write("}\n")

        with open(os.path.join(builddir, f"PySyntaxBindings{i}.cpp"), "w") as f:
            f.write(outf.getvalue())


def generatePyFactoryBindings(builddir, alltypes):
    """Generate Python bindings for SyntaxFactory class and all its methods."""

    outf = StringIO()
    outf.write(
        """//------------------------------------------------------------------------------
// PySyntaxFactory.cpp
// Generated Python bindings for SyntaxFactory
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/syntax/AllSyntax.h"

void registerSyntaxFactory(nb::module_& m) {
    nb::class_<SyntaxFactory>(m, "SyntaxFactory",
        "Factory for creating syntax nodes. Access via SyntaxRewriter.factory.")
"""
    )

    factory_methods = []
    for name, typeinfo in sorted(alltypes.items()):
        if name == "SyntaxNode":
            continue
        if not typeinfo.final:
            continue
        factory_methods.append((name, typeinfo))

    methods_by_letter = {}
    for name, typeinfo in factory_methods:
        first_letter = name[0].upper()
        if first_letter not in methods_by_letter:
            methods_by_letter[first_letter] = []
        methods_by_letter[first_letter].append((name, typeinfo))

    for letter in sorted(methods_by_letter.keys()):
        outf.write(f"\n        // --- {letter} ---\n")
        for name, typeinfo in methods_by_letter[letter]:
            method_name = name
            method_name = method_name.removesuffix("Syntax")
            method_name = method_name[0].lower() + method_name[1:]

            outf.write(f'        .def("{method_name}", &SyntaxFactory::{method_name}')
            # `byrefint` is the nanobind rv_policy::reference_internal alias
            # defined in pyslang.h (included by the generated files).
            outf.write(", byrefint")

            for arg in typeinfo.argNames:
                if arg in typeinfo.optionalMembers:
                    for m in typeinfo.combinedMembers:
                        if m[MEMBER_NAME] == arg:
                            if len(m) <= MEMBER_BASE_TYPE:
                                raise ValueError(
                                    f"Optional member '{arg}' in '{name}' is missing base type"
                                    f" information (expected at index {MEMBER_BASE_TYPE})"
                                )
                            base_type = m[MEMBER_BASE_TYPE]
                            outf.write(
                                f', nb::arg("{arg}").none() = static_cast<{base_type}*>(nullptr)'
                            )
                            break
                else:
                    outf.write(f', "{arg}"_a')

            outf.write(")\n")

    outf.write("    ;\n")
    outf.write("}\n")
    with open(os.path.join(builddir, "PySyntaxFactory.cpp"), "w") as f:
        f.write(outf.getvalue())


def generateCSTJson(builddir, alltypes):
    cppf = StringIO()

    # Generate handle() methods for all leaf syntax types
    for typename, typeinfo in sorted(alltypes.items()):
        if typename == "SyntaxNode":
            continue

        # Only generate for leaf types
        if typeinfo.final == "":
            continue

        if not typeinfo.combinedMembers:
            continue

        cppf.write(f"""
    void handle(const {typename}& node) {{
""")

        # Generate code for each member (including inherited)
        for member in typeinfo.combinedMembers:
            memberType, memberName = member[MEMBER_TYPE], member[MEMBER_NAME]

            # Check if member is optional
            isOptional = memberName in typeinfo.optionalMembers

            if isOptional:
                if memberType == "Token":
                    raise ValueError(
                        f"Token member '{memberName}' in type '{typename}' cannot be optional; there are no optional tokens."
                    )
                else:
                    cppf.write(
                        f'        writeOptionalNode("{memberName}", node.{memberName});\n'
                    )
            else:
                if memberType == "Token":
                    cppf.write(
                        f'        writeToken("{memberName}", node.{memberName});\n'
                    )
                elif memberType.startswith("SeparatedSyntaxList<"):
                    cppf.write(
                        f'        writeSeparatedSyntaxList("{memberName}", node.{memberName});\n'
                    )
                elif memberType.startswith("SyntaxList<"):
                    cppf.write(
                        f'        writeSyntaxList("{memberName}", node.{memberName});\n'
                    )
                elif memberType == "TokenList":
                    cppf.write(
                        f'        writeTokenList("{memberName}", node.{memberName});\n'
                    )
                else:
                    cppf.write(
                        f'        writeNode("{memberName}", node.{memberName});\n'
                    )

        cppf.write("    }\n")
        cppf.write("    \n")

    with open(
        os.path.join(builddir, "slang", "syntax", "CSTJsonVisitorGen.h"), "w"
    ) as f:
        f.write(cppf.getvalue())


if __name__ == "__main__":
    main()
