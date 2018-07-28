#!/bin/bash
set -ev
export ASAN_SYMBOLIZER_PATH=/usr/lib/llvm-6.0/bin/llvm-symbolizer
cd /slang
make -C build -j 8
build/bin/unittests
bash <(curl -s https://codecov.io/bash) -x 'llvm-cov-6.0 gcov' -a '1> /dev/null 2> /dev/null' || echo 'Codecov failed to upload'
FILES=$(find source -type f -name '*.cpp')
for f in $FILES; do
	/usr/lib/llvm-6.0/bin/clang-tidy $f -quiet -checks=-*,clang-analyzer-*,bugprone-*,performance-*,modernize-*,-modernize-use-auto -- -Isource -Iexternal -I. -std=c++1z;
done
