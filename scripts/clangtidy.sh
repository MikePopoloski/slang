#!/bin/bash
set -v
/usr/lib/llvm-5.0/bin/clang-tidy -version
FILES=$(find source -type f -name '*.cpp')
for f in $FILES; do
	/usr/lib/llvm-5.0/bin/clang-tidy $f -quiet -checks=-*,clang-analyzer-*,bugprone-*,performance-*,modernize-*,-modernize-use-auto -- -Isource -Iexternal -I. -std=c++1z;
done
