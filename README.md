## slang - SystemVerilog Language Services

Parser and compiler library for SystemVerilog.

Still under heavy construction!

### Goals

* Fully parse and analyze all SystemVerilog features.
* Be robust about compilation, no matter how broken the source text. This makes the compiler usable in editor highlighting and completion scenarios, where the code is likely to be pretty broken.
* The parse tree should round trip back to the original source, making it easy to write refactoring and code generation tools.
* Provide great error messages, ala clang.
* Be fast and robust in the face of production-scale projects.
