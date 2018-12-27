#!/bin/bash
set -ev
cd /slang
mkdir build
cd build
s=$(realpath ../scripts/cppcheck_suppressions.txt)
cmake -DCMAKE_CXX_COMPILER=g++-8 -DCMAKE_BUILD_TYPE=Debug "-DCMAKE_CXX_CPPCHECK=/tmp/cppcheck/cppcheck;-q;--enable=warning,performance,portability;--suppressions-list=$s" ..
make -j 8
ctest
cd ..
#bash <(curl -s https://codecov.io/bash) -x 'gcov-8' -a '1> /dev/null 2> /dev/null' || echo 'Codecov failed to upload'