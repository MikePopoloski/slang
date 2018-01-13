#!/bin/bash
set -ev
export ASAN_SYMBOLIZER_PATH=/usr/lib/llvm-5.0/bin/llvm-symbolizer
cd /slang
make -C build/projects/gmake-linux-clang -j 4 CXX=clang++-5.0
build/linux64_clang/bin/unittestsDebug
FILES=$(find source -type f -name '*.cpp')
for f in $FILES; do
	/usr/lib/llvm-5.0/bin/clang-tidy $f -quiet -checks=-*,clang-analyzer-*,bugprone-*,performance-*,modernize-*,-modernize-use-auto -- -Isource -Iexternal -I. -std=c++1z;
done