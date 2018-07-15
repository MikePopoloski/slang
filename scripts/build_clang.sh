#!/bin/bash
set -ev
export ASAN_SYMBOLIZER_PATH=/usr/lib/llvm-6.0/bin/llvm-symbolizer
cd /slang
make -C build -j 8
build/tests/unittests/unittests
bash <(curl -s https://codecov.io/bash) -x 'llvm-cov-6.0 gcov' -X gcovout || echo 'Codecov failed to upload'
FILES=$(find source -type f -name '*.cpp')
for f in $FILES; do
	/usr/lib/llvm-6.0/bin/clang-tidy $f -quiet -checks=-*,clang-analyzer-*,bugprone-*,performance-*,modernize-*,-modernize-use-auto -- -Isource -Iexternal -I. -std=c++1z;
done