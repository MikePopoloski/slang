#!/usr/bin/env python
# This script deletes the given directory and everything within it.
# cmake makes this difficult so here we are.
import shutil
import sys


def main():
    shutil.rmtree(sys.argv[1], ignore_errors=True)


if __name__ == "__main__":
    main()
