import os
def generateSyntaxFactory(builddir, alltypes):
    bindingsdir = "../slang/bindings/python"
    outf = open(os.path.join(builddir,bindingsdir, "SyntaxFactoryBindings.cpp"), "w")
    print("location", os.path.join(builddir,bindingsdir, "SyntaxFactoryBindings.cpp"))
    outf.write("""
//------------------------------------------------------------------------------
//! @file SyntaxFactoryBindings.cpp
//! @brief Generated SyntaxFactoryBindings 
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------\n""")
    outf.write('''#include "pyslang.h"
#include "slang/syntax/AllSyntax.h"

void registerFactory(py::module_& m) {
    py::class_<SyntaxFactory> SyntaxFactory(m, "SyntaxFactory");
    SyntaxFactory.def(py::init<BumpAllocator&>(), "alloc"_a);
''')
    for k, v in sorted(alltypes.items()):
        if not v.final:
            continue

        methodName = k
        if methodName.endswith("Syntax"):
            methodName = methodName[:-6]
        methodName = methodName[:1].lower() + methodName[1:]
        outf.write(f'    SyntaxFactory.def("{methodName}",&SyntaxFactory::{methodName}')
        arguments= v.constructorArgs.split(",")
        for argument in arguments:
            # type and name separated
            argument_splitted = argument.split(" ")
            if argument_splitted[0] == 'Token':
                outf.write(f' ,py::arg("{argument_splitted[1]}") = Token()')
            else:
                outf.write(f' ,py::arg("{argument_splitted[1]}") = nullptr')

        outf.write(");\n")
        
    outf.write("};")
    outf.close()

