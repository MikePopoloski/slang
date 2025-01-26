slang-threadtest
================
A simple tool that allows testing the thread safety invariants of the AST.
The AST, once an initial visitation has occurred and all diagnostics are collected,
should then be able to be visited from multiple threads without issue. This tool
runs many such visitations across a design to see if any asserts fire.

Usage:

```
slang-threadtest [-n num_iterations] <all-other-slang-args>
```
