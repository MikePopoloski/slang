#!/bin/bash
set -ev
make -C /slang/build/projects/gmake-linux-clang -j 4 CXX=clang++-5.0
/slang/build/linux64_clang/bin/unittestsDebug
FILES=$(find source -type f -name '*.cpp')
for f in $FILES; do
	/usr/lib/llvm-5.0/bin/clang-tidy $f -quiet -checks=-*,clang-analyzer-*,bugprone-*,performance-*,modernize-*,-modernize-use-auto -- -Isource -Iexternal -I. -std=c++1z;
done