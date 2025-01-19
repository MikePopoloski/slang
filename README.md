slang - SystemVerilog Language Services
=======================================
![](https://github.com/MikePopoloski/slang/workflows/CI%20Build/badge.svg)
[![codecov](https://codecov.io/gh/MikePopoloski/slang/branch/master/graph/badge.svg)](https://codecov.io/gh/MikePopoloski/slang)
[![PyPI](https://img.shields.io/pypi/v/pyslang.svg)](https://pypi.org/project/pyslang/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://github.com/MikePopoloski/slang/blob/master/LICENSE)

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

Instructions on building slang from source are [here](https://sv-lang.com/building.html). The tl;dr is:
```
git clone https://github.com/MikePopoloski/slang.git
cd slang
cmake -B build
cmake --build build -j
```

The slang binary can be run on your code right out of the box; check out the [user manual](https://sv-lang.com/user-manual.html) for more information about how it works.

If you're looking to use slang as a library, please read through the [developer guide](https://sv-lang.com/developer-guide.html).

### Try It Out

Experiment with parsing, type checking, and error detection live [on the web](https://sv-lang.com/explore/) (inspired by Matt Godbolt's excellent [Compiler Explorer](https://godbolt.org/)).

### Python Bindings

This project also includes Python bindings for the library, which can be installed via PyPI:
```
pip install pyslang
```
or, to update your installed version to the latest release:
```
pip install -U pyslang
```
or, to checkout and install a local build:
```
git clone https://github.com/MikePopoloski/slang.git
cd slang
pip install .
```

#### Example Python Usage

Given a 'test.sv' source file:
```sv
module memory(
    address,
    data_in,
    data_out,
    read_write,
    chip_en
  );

  input wire [7:0] address, data_in;
  output reg [7:0] data_out;
  input wire read_write, chip_en;

  reg [7:0] mem [0:255];

  always @ (address or data_in or read_write or chip_en)
    if (read_write == 1 && chip_en == 1) begin
      mem[address] = data_in;
  end

  always @ (read_write or chip_en or address)
    if (read_write == 0 && chip_en)
      data_out = mem[address];
    else
      data_out = 0;

endmodule
```

We can use slang to load the syntax tree and inspect it:
```py
import pyslang

tree = pyslang.SyntaxTree.fromFile('test.sv')
mod = tree.root.members[0]
print(mod.header.name.value)
print(mod.members[0].kind)
print(mod.members[1].header.dataType)
```

```
memory
SyntaxKind.PortDeclaration
reg [7:0]
```

We can also evaluate arbitrary SystemVerilog expressions:
```py
session = pyslang.ScriptSession()
session.eval("logic bit_arr [16] = '{0:1, 1:1, 2:1, default:0};")
result = session.eval("bit_arr.sum with ( int'(item) );")
print(result)
```

```
3
```

### Contact & Support

If you encounter a bug, have questions, or want to contribute, please get in touch by opening a GitHub issue or discussion thread.

Contributions are welcome, whether they be in the form of bug reports, comments, suggestions, documentation improvements, or full fledged new features via pull requests.

### License

slang is licensed under the MIT license:

>   Copyright (c) 2015-2025 Michael Popoloski
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
