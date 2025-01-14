# pyslang - Language bindings for slang, SystemVerilog parsing and compilation library

[![build](https://github.com/MikePopoloski/pyslang/actions/workflows/build.yml/badge.svg)](https://github.com/MikePopoloski/pyslang/actions/workflows/build.yml)
[![PyPI](https://img.shields.io/pypi/v/pyslang.svg)](https://pypi.org/project/pyslang/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://github.com/MikePopoloski/pyslang/blob/master/LICENSE)
[![Join the chat at https://gitter.im/MikePopoloski/slang](https://badges.gitter.im/MikePopoloski/slang.svg)](https://gitter.im/MikePopoloski/slang?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

slang is a software library that provides various components for lexing, parsing, type checking, and elaborating SystemVerilog code. pyslang exposes that library
to Python projects.

Full documentation is available on the website: https://sv-lang.com

## Installation
pyslang can be installed like any other Python library, using (a recent version of) the Python package manager `pip`, on Linux, macOS, and Windows:
```
pip install pyslang
```
or, to update your installed version to the latest release:
```
pip install -U pyslang
```
or, to checkout and install a local build:
```
git clone https://github.com/MikePopoloski/pyslang.git
cd pyslang
git submodule update --init --recursive
pip install .
```

## Example usage

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

## Contact & Support

If you encounter a bug, have questions, or want to contribute, please get in touch by opening a GitHub issue or posting a message on Gitter.

Contributions are welcome, whether they be in the form of bug reports, comments, suggestions, documentation improvements, or full fledged new features via pull requests.

## License

slang (and pyslang) is licensed under the MIT license:

>   Copyright (c) 2015-2024 Michael Popoloski
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
