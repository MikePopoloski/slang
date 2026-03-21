# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

target_sources(slang_slang PRIVATE CodeGenerator.cpp ExprEmitter.cpp
                                   SysCallEmitter.cpp StmtEmitter.cpp JIT.cpp)
