#!/bin/bash
set -ev
cd /slang
mkdir build
cd build
cmake -DCMAKE_CXX_COMPILER=g++-8 -DCMAKE_BUILD_TYPE=Debug -DCI_BUILD=ON ..
make -j 8
ctest
