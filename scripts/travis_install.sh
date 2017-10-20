#!/bin/bash

# Set symlinks for up to date compilers
mkdir -p latest-symlinks
ln -s /usr/bin/clang++-5.0 latest-symlinks/clang++
ln -s /usr/bin/clang-5.0 latest-symlinks/clang
ln -s /usr/bin/g++-7 latest-symlinks/g++
ln -s /usr/bin/gcc-7 latest-symlinks/gcc
ln -s /usr/bin/gcov-7 latest-symlinks/gcov
export PATH=$PWD/latest-symlinks:$PATH

# Print compiler versions so that we know for sure what we're running
clang++ --version
g++ --version

# Generate project files
tools/bin/linux/genie --gcc=$BUILD_TARGET --with-coverage gmake

# Download and build cppcheck
wget http://github.com/danmar/cppcheck/releases/download/1.81/cppcheck-1.81.tar.gz
tar xvzf cppcheck-1.81.tar.gz
make -j 4 -C cppcheck-1.81