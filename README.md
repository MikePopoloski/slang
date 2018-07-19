slang - SystemVerilog Language Services
=======================================
[![Build Status](https://travis-ci.org/MikePopoloski/slang.svg?branch=master)](https://travis-ci.org/MikePopoloski/slang)
[![Build status](https://ci.appveyor.com/api/projects/status/n86l5nuq5nw9on0u/branch/master?svg=true)](https://ci.appveyor.com/project/MikePopoloski/slang/branch/master)
[![codecov](https://codecov.io/gh/MikePopoloski/slang/branch/master/graph/badge.svg)](https://codecov.io/gh/MikePopoloski/slang)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://github.com/MikePopoloski/slang/blob/master/LICENSE) [![Join the chat at https://gitter.im/MikePopoloski/slang](https://badges.gitter.im/MikePopoloski/slang.svg)](https://gitter.im/MikePopoloski/slang?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

Parser and compiler library for SystemVerilog.

Still under heavy construction!

### Goals
* Fully parse and analyze all SystemVerilog features.
* Be robust about compilation, no matter how broken the source text. This makes the compiler usable in editor highlighting and completion scenarios, where the code is likely to be pretty broken.
* The parse tree should round trip back to the original source, making it easy to write refactoring and code generation tools.
* Provide great error messages, ala clang.
* Be fast and robust in the face of production-scale projects.

### Build Instructions

#### Dependencies
- [python 3](https://www.python.org/)
- [conan](https://conan.io/)
- [CMake](https://cmake.org/) (3.10 or later)
- C++17 compatible compiler

#### Compilation
CMake is used for project generation and Conan is used for dependency management. All external packages will be pulled down, configured, and built automatically by Conan as part of invoking CMake. CMake supports many generator backends so use the one that is most comfortable for you; some recommended options are as follows:

##### Visual Studio
The recommended method on Windows is to open the slang root folder in Visual Studio and press build. The IDE handles all of the CMake interaction.

##### Ninja
[Ninja](https://ninja-build.org/) is the recommended method for command line building (on any platform):
```
mkdir build && cd build
cmake -GNinja ..
ninja
```

##### Make
If you're building on Linux and don't want the additional Ninja dependency, you can build with make, which is the default generator for CMake on Linux:
```
mkdir build && cd build
cmake ..
make -j 8
```

#### Running tests
From the build directory:
```
bin/unittests
```