#!/bin/bash
set -ev
cd /slang
make -C build -j 8
build/bin/unittests
bash <(curl -s https://codecov.io/bash) -x 'gcov-8' -a '1> /dev/null 2> /dev/null' || echo 'Codecov failed to upload'
/tmp/cppcheck/cppcheck source -I. -Iexternal -Isource -q --enable=warning,performance,portability --inconclusive --suppressions-list=scripts/cppcheck_suppressions.txt
