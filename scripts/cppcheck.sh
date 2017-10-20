#!/bin/bash
set -ev
cppcheck-1.81/cppcheck source -I. -Iexternal -Isource -q --enable=warning,performance,portability --inconclusive --suppress=*:external/fmt/format.h --suppress=*:external/fmt/format.cc