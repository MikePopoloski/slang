slang - SystemVerilog Language Services
=======================================
![](https://github.com/MikePopoloski/slang/workflows/CI%20Build/badge.svg)
[![codecov](https://codecov.io/gh/MikePopoloski/slang/branch/master/graph/badge.svg)](https://codecov.io/gh/MikePopoloski/slang)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://github.com/MikePopoloski/slang/blob/master/LICENSE)
[![Join the chat at https://gitter.im/MikePopoloski/slang](https://badges.gitter.im/MikePopoloski/slang.svg)](https://gitter.im/MikePopoloski/slang?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

slang is a software library that provides various components for lexing, parsing, type checking, and elaborating SystemVerilog code. It comes with an executable tool that can compile and lint any SystemVerilog project, but it is also intended to be usable as a front end for synthesis tools, simulators, linters, code editors, and refactoring tools.

slang is the fastest and most compliant SystemVerilog frontend (according to the open source [chipsalliance test suite](https://github.com/chipsalliance/sv-tests)).

Full documentation is available on the website: https://sv-lang.com

### Features
-   Fully parse, analyze, and elaborate all SystemVerilog features - see [this page](https://sv-lang.com/language-support.html) for current status.
-   Be robust about compilation, no matter how broken the source text. This makes the compiler usable in editor highlighting and completion scenarios, where the code is likely to be broken because the user is still writing it.
-   The parse tree should round trip back to the original source, making it easy to write refactoring and code generation tools.
-   Provide great error messages, ala clang.
-   Be fast and robust in the face of production-scale projects.

### Use Cases
Some examples of things you can use slang for:
-   Very fast syntax checking and linting tool
-   Dumping the AST of your project to JSON
-   Source code introspection via included Python bindings
-   SystemVerilog code generation and refactoring
-   As the engine for an editor language server
-   As a fast and robust preprocessor that sits in front of downstream tools
-   As a frontend for a synthesis or simulation tool, by including slang as a library

### Getting Started

Instructions on building slang from source are [here](https://sv-lang.com/building.html).

The slang binary can be run on your code right out of the box; check out the [user manual](https://sv-lang.com/user-manual.html) for more information about how it works.

If you're looking to use slang as a library, please read through the [developer guide](https://sv-lang.com/developer-guide.html).

### Try It Out

Experiment with parsing, type checking, and error detection live [on the web](https://sv-lang.com/explore/) (inspired by Matt Godbolt's excellent [Compiler Explorer](https://godbolt.org/)).

### Contact & Support

If you encounter a bug, have questions, or want to contribute, please get in touch by opening a GitHub issue or discussion thread.

Contributions are welcome, whether they be in the form of bug reports, comments, suggestions, documentation improvements, or full fledged new features via pull requests.

### License

slang is licensed under the MIT license:

>   Copyright (c) 2015-2023 Michael Popoloski
>
>   Permission is hereby granted, free of charge, to any person obtaining a copy
>   of this software and associated documentation files (the "Software"), to deal
>   in the Software without restriction, including without limitation the rights
>   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
>   copies of the Software, and to permit persons to whom the Software is
>   furnished to do so, subject to the following conditions:
>
>   The above copyright notice and this permission notice shall be included in
>   all copies or substantial portions of the Software.
>
>   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
>   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
>   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
>   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
>   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
>   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
>   THE SOFTWARE.
