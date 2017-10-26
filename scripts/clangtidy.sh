#!/bin/bash
set -v
clang-tidy -version
FILES=$(find source -type f -name '*.cpp')
for f in $FILES; do
	clang-tidy $f -checks=-*,clang-analyzer-*,bugprone-*,performance-*,modernize-*,-modernize-use-auto -- -Isource -Iexternal -I. -std=c++1z;
done
