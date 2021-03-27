#!/bin/bash
set -e
set -x
TESTS=`ls ~/git/sv-tests/tests/chapter-16/*.sv`
TESTS=`ls ~/git/sv-tests/tests/chapter-16/*property-loc*.sv`
TESTS+=" "
TESTS+=`ls ~/git/sv-tests/tests/chapter-8/*.sv`

TESTS=`ls \
    ~/git/sv-tests/tests/chapter-16/16.12--property-disable-iff.sv \
    ~/git/sv-tests/tests/chapter-16/16.12--property-disj.sv \
    ~/git/sv-tests/tests/chapter-16/16.12--property-iff.sv \
    ~/git/sv-tests/tests/chapter-16/16.12--property-prec.sv \
    ~/git/sv-tests/tests/chapter-16/16.12--property.sv \
    ~/git/sv-tests/tests/chapter-16/16.14--assume-property.sv \
    ~/git/sv-tests/tests/chapter-16/16.15--property-disable-iff-fail.sv \
    ~/git/sv-tests/tests/chapter-16/16.15--property-disable-iff.sv \
    ~/git/sv-tests/tests/chapter-16/16.17--expect.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--assert0.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--assert-final.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--assert.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--assume0.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--assume-final.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--assume.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--cover0.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--cover-final.sv \
    ~/git/sv-tests/tests/chapter-16/16.2--cover.sv \
    ~/git/sv-tests/tests/chapter-16/16.7--sequence.sv \
    ~/git/sv-tests/tests/chapter-16/16.9--sequence-cons-repetition.sv \
    ~/git/sv-tests/tests/chapter-16/16.9--sequence-goto-repetition.sv \
    ~/git/sv-tests/tests/chapter-16/16.9--sequence-noncons-repetition.sv \
    `

UVMDIR=~/git/uvm/src
#UVMPKG=$UVMDIR/uvm_pkg.sv
JSONDIR=json

mkdir -p $JSONDIR
for file in $TESTS; do
    echo "######" $file "######"
    outfile=`basename $file`
    ~/git/slang/build/bin/slang -I $UVMDIR -y $UVMDIR --ast-json $JSONDIR/$outfile `echo $file` $UVMPKG | grep -v BADBBDBDBDBD
#    ~/git/Surelog/build/bin/surelog $file
    echo
#break
done
