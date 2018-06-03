#!/bin/bash
set -ev
cd /slang
make -C build/projects/gmake-linux -j 4 CXX=g++-8
build/linux64_gcc/bin/unittestsDebug;
/tmp/cppcheck/cppcheck source -I. -Iexternal -Isource -q --enable=warning,performance,portability --inconclusive --suppressions-list=scripts/cppcheck_suppressions.txt
