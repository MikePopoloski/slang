#!/bin/bash
set -ev
export ASAN_SYMBOLIZER_PATH=/usr/lib/llvm-6.0/bin/llvm-symbolizer
cd /slang
mkdir build
cd build
cmake -DCMAKE_CXX_COMPILER=clang++-6.0 -DSLANG_COVERAGE=ON -DSLANG_SANITIZERS=undefined,address "-DCMAKE_CXX_CLANG_TIDY=/usr/lib/llvm-6.0/bin/clang-tidy;-quiet;-checks=-*,clang-analyzer-*,bugprone-*,performance-*,modernize-*,-modernize-use-auto,-modernize-raw-string-literal,misc-*" ..
make -j 8
ctest
bash <(curl -s https://codecov.io/bash) -x 'llvm-cov-6.0 gcov' -a '1> /dev/null 2> /dev/null' || echo 'Codecov failed to upload'
