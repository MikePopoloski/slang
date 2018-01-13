#!/bin/bash
set -ev
cd /slang
make -C build/projects/gmake-linux -j 4 CXX=g++-7
build/linux64_gcc/bin/unittestsDebug;
/tmp/cppcheck/cppcheck source -I. -Iexternal -Isource -q --enable=warning,performance,portability --inconclusive --suppressions-list=cppcheck_suppressions.txt
bash <(curl -s https://codecov.io/bash) || echo 'Codecov failed to upload'