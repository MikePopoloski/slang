#!/usr/bin/env python3
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import subprocess
import sys
import tempfile
from pathlib import Path

INPUT_LINES = [
    "module top;",
    "`ifdef UNKNOWN",
    "  logic unknown;",
    "`elsif FORCED",
    "  logic forced;",
    "`endif",
    "endmodule",
]

EXPECTED_LINES = [
    "module top;",
    "`ifdef UNKNOWN",
    "  logic unknown;",
    "`else",
    "  logic forced;",
    "`endif",
    "endmodule",
]


def join_lines(lines: list[str], newline: bytes) -> bytes:
    return newline.join(line.encode() for line in lines) + newline


def main() -> int:
    if len(sys.argv) < 2:
        print(f"usage: {sys.argv[0]} <command> [args...]", file=sys.stderr)
        return 2

    command = sys.argv[1:]
    with tempfile.TemporaryDirectory(prefix="slang_unifdef_newlines_") as temp_dir:
        for name, newline in (("lf", b"\n"), ("crlf", b"\r\n"), ("cr", b"\r")):
            source = Path(temp_dir) / f"{name}.sv"
            source.write_bytes(join_lines(INPUT_LINES, newline))

            result = subprocess.run(
                [*command, "--define", "FORCED", source],
                capture_output=True,
                check=False,
            )
            if result.returncode != 0:
                print(result.stderr.decode(errors="replace"), file=sys.stderr)
                return result.returncode

            expected = join_lines(EXPECTED_LINES, newline)
            actual = result.stdout
            if actual != expected:
                print(f"{name}: newline-preserving output mismatch", file=sys.stderr)
                print(f"expected: {expected!r}", file=sys.stderr)
                print(f"actual:   {actual!r}", file=sys.stderr)
                return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
