#!/bin/bash
set -ev
cd /slang
make -C build -j 8
build/tests/unittests/unittests
/tmp/cppcheck/cppcheck source -I. -Iexternal -Isource -q --enable=warning,performance,portability --inconclusive --suppressions-list=scripts/cppcheck_suppressions.txt
