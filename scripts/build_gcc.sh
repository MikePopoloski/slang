#!/bin/bash
set -ev
cd /slang
mkdir build
cd build
s=$(realpath ../scripts/cppcheck_suppressions.txt)
cmake -DCMAKE_CXX_COMPILER=g++-8 -DCMAKE_BUILD_TYPE=Debug -DCI_BUILD=ON "-DCMAKE_CXX_CPPCHECK=/tmp/cppcheck/cppcheck;-q;--enable=warning,performance,portability;--suppressions-list=$s" ..
make -j 8
ctest
