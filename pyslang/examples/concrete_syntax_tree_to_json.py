# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import sys

import pyslang


def main():
    tree = pyslang.SyntaxTree.fromFile(sys.argv[1])

    json_output = tree.root.to_json()
    print(json_output)


if __name__ == "__main__":
    main()
