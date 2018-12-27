#!/bin/bash
set -ev
export ASAN_SYMBOLIZER_PATH=/usr/lib/llvm-7/bin/llvm-symbolizer
cd /slang
mkdir build
cd build
cmake -DCMAKE_CXX_COMPILER=clang++-7 -DCMAKE_BUILD_TYPE=Debug -DSLANG_COVERAGE=ON -DSLANG_SANITIZERS=undefined,address "-DCMAKE_CXX_CLANG_TIDY=/usr/lib/llvm-7/bin/clang-tidy;-quiet;-checks=-*,clang-analyzer-*,bugprone-*,performance-*,modernize-*,-modernize-use-auto,-modernize-raw-string-literal,-bugprone-suspicious-semicolon,-clang-analyzer-cplusplus.NewDelete*,-clang-analyzer-cplusplus.InnerPointer,misc-*" ..
make -j 8
export LLVM_PROFILE_FILE=%p.profraw
ctest
find . -name *.profraw -exec llvm-profdata-7 merge -o merged.profdata -sparse {} + ;
llvm-cov-7 show bin/unittests -instr-profile=merged.profdata > coverage.txt
bash <(curl -s https://codecov.io/bash) || echo 'Codecov failed to upload'