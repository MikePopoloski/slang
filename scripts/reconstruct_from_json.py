#!/usr/bin/env python3
#
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

"""
Reconstructs source code from CST JSON output to verify token completeness.

This script extracts all tokens (including separators from SeparatedSyntaxList
nodes) from the CST JSON and reconstructs the original source code to verify
that all tokens are properly captured in the JSON output.
"""

import argparse
import json
import sys


def extract_tokens(node, tokens):
    """Recursively extract all tokens from a CST node in order."""
    if node is None:
        return

    # Text that comes from a macro expansion or an included file is serialized in addition
    # to the directive that produced it (which occupies the same source position), so skip
    # it to reconstruct the original, unexpanded source. This flag is set on both tokens
    # and their plain-text trivia. Note directive trivia carry no "text" of their own, so
    # even when they sit inside expanded content they are still recursed into below (the
    # producing `include / macro usage lives there).
    expanded = isinstance(node, dict) and node.get("fromExpansion")

    if isinstance(node, dict):
        # Check if this is a token node
        if "kind" in node and "text" in node:
            # Always process trivia first (it may itself contain directive syntax, e.g.
            # `ifdef branches whose disabled tokens hang off the directive, or the
            # `include / macro usage that produced an expansion) followed by the token's
            # own text.
            if "trivia" in node:
                for trivia in node["trivia"]:
                    extract_tokens(trivia, tokens)
            if not expanded:
                tokens.append(node["text"])
        else:
            # This is a syntax node (or a piece of trivia) - recurse through all
            # properties. This covers directive trivia, whose content lives under a
            # nested "syntax" node rather than a flat "text" field.
            for key, value in node.items():
                if key in ["kind"]:  # Skip metadata
                    continue
                extract_tokens(value, tokens)
    elif isinstance(node, list):
        for item in node:
            extract_tokens(item, tokens)


def reconstruct_source(json_file):
    """Read CST JSON and reconstruct the original source code."""
    with open(json_file, "r") as f:
        data = json.load(f)

    tokens = []

    # Handle the top-level structure
    if "syntaxTrees" in data:
        for tree in data["syntaxTrees"]:
            extract_tokens(tree, tokens)
    else:
        # Direct CST node
        extract_tokens(data, tokens)

    # Join all tokens to reconstruct source
    reconstructed = "".join(tokens)

    return reconstructed, len(tokens)


def main():
    parser = argparse.ArgumentParser(
        description="Reconstruct source code from CST JSON"
    )
    parser.add_argument("json_file", help="CST JSON file to read")
    parser.add_argument("--output", "-o", help="Output file (default: stdout)")
    parser.add_argument(
        "--compare", "-c", help="Original source file to compare against"
    )
    parser.add_argument(
        "--stats", "-s", action="store_true", help="Show token statistics"
    )

    args = parser.parse_args()

    try:
        reconstructed, token_count = reconstruct_source(args.json_file)

        if args.output:
            with open(args.output, "w") as f:
                f.write(reconstructed)
            print(f"Reconstructed source written to {args.output}")
        else:
            print(reconstructed, end="")

        if args.stats:
            print("\nStatistics:", file=sys.stderr)
            print(f"  Total tokens extracted: {token_count}", file=sys.stderr)
            print(f"  Total characters: {len(reconstructed)}", file=sys.stderr)

        if args.compare:
            with open(args.compare, "r") as f:
                original = f.read()

            if reconstructed == original:
                print("\n✓ Perfect match with original file!", file=sys.stderr)
                return 0
            else:
                print("\n✗ Mismatch with original file:", file=sys.stderr)
                print(f"  Original: {len(original)} chars", file=sys.stderr)
                print(f"  Reconstructed: {len(reconstructed)} chars", file=sys.stderr)

                # Show first difference
                for i, (a, b) in enumerate(zip(original, reconstructed)):
                    if a != b:
                        print(
                            f"  First difference at position {i}: '{a}' vs '{b}'",
                            file=sys.stderr,
                        )
                        break

                return 1

        return 0

    except Exception as e:  # noqa: BLE001 - CLI boundary reports any failure and exits
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
