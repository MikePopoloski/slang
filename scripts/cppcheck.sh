#!/bin/bash
set -ev
cppcheck-1.81/cppcheck source -I. -Iexternal -Isource -q --enable=warning,performance,portability --inconclusive --suppressions-list=scripts/cppcheck_suppressions.txt