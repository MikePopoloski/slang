slang - SystemVerilog Language Services
=======================================
[![Build Status](https://travis-ci.org/MikePopoloski/slang.svg?branch=master)](https://travis-ci.org/MikePopoloski/slang)
[![Build status](https://ci.appveyor.com/api/projects/status/n86l5nuq5nw9on0u/branch/master?svg=true)](https://ci.appveyor.com/project/MikePopoloski/slang/branch/master)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://github.com/MikePopoloski/slang/blob/master/LICENSE)

Parser and compiler library for SystemVerilog.

Still under heavy construction!

### Goals

* Fully parse and analyze all SystemVerilog features.
* Be robust about compilation, no matter how broken the source text. This makes the compiler usable in editor highlighting and completion scenarios, where the code is likely to be pretty broken.
* The parse tree should round trip back to the original source, making it easy to write refactoring and code generation tools.
* Provide great error messages, ala clang.
* Be fast and robust in the face of production-scale projects.

### Build Instructions

You need a compiler for your platform that supports C++17. The tests run under Visual Studio 2017, GCC-6, and Clang-3.9.

#### Windows
```
tools/bin/windows/genie vs2017
msbuild build/projects/vs2017/slang.sln
```

#### Linux - GCC
```
tools/bin/linux/genie --gcc=linux-gcc-6 gmake
make -C build/projects/gmake-linux -j 8
```

#### Linux - Clang
```
tools/bin/linux/genie --gcc=linux-clang gmake
make -C build/projects/gmake-linux-clang -j 8
```
