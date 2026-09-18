#!/usr/bin/env python3
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

"""slang-lit: Lightweight test runner for slang regression tests.

Test files are SystemVerilog source files (or plain-text files) containing
special comment directives. The format is inspired by LLVM's lit + FileCheck.

Directives in test files
------------------------
  // RUN: <command>           Run a shell command. The stdout of all RUN
                              commands for the file is collected and fed into
                              the CHECK engine below.

  // CHECK: <pattern>         A line in the output must match <pattern> (regex).
                              Patterns are matched in order of appearance.

  // CHECK-NEXT: <pattern>    The line immediately following the previous CHECK
                              match must also match <pattern>.

  // CHECK-NOT: <pattern>     No line in the output between the current and the
                              next positive CHECK must match <pattern>.

  // CHECK-DAG: <pattern>     Like CHECK, but the patterns in a DAG group may
                              match in any order (relative ordering among
                              CHECK-DAG directives is not enforced).

  // CHECK-LABEL: <pattern>   Resets the current scan position to the matching
                              line. Useful for separating sections.

  // CHECK-DIAGS: <file>      Check JSON diagnostics in <file> against inline
                              squiggle annotations. The file is normally
                              produced with ``%slang --diag-json %t``.

Inline diagnostic annotations are placed directly below the source line they
describe. The ``//`` starts in column 1 and carets use their physical source
columns, so they visually align with the highlighted text. Continuation ranges
and notes identify their primary diagnostic with a ``- for`` suffix::

        int scalar;
    //      ^ NoteDeclarationHere declared here - for AssignmentPatternNoMember(scalar)
        value = '{real: 1.0};
    //          ^^ AssignmentPatternNoMember member 'scalar' is not covered by any assignment pattern key

Multiple diagnostics on the same source line use one annotation line each.

Pass ``--update-diags`` to generate or refresh these annotations from the JSON
diagnostics emitted by each test's RUN command. Updated tests are rerun immediately
to verify the generated expectations.

  // XFAIL: *                 Mark the test as expected to fail.

  // REQUIRES: llvm           Skip the test unless a requirement is satisfied.

Substitutions in RUN lines
---------------------------
  %s      Absolute path to the test source file.
  %t      Path to a per-test temporary file (cleaned up after each test).
  %T      Temporary directory shared for the test run.
  %slang  Path to the slang binary (configurable via --slang).
  %KEY    User-defined substitution introduced via --define KEY=VALUE.

Usage
-----
  slang-lit.py [options] <test-file-or-dir> ...

Options
-------
  --slang <path>        Path to the slang binary (default: searches PATH, then
                        common build directories relative to the script location).
  --define KEY=VALUE    Define a custom substitution; %KEY in RUN lines is
                        replaced with VALUE. Can be specified multiple times.
  --verbose, -v         Print each test command as it runs.
  --jobs, -j <N>        Run N tests in parallel (default: one per usable CPU).
  --filter <regex>      Run only tests whose paths match <regex>.
  --update-diags        Rewrite inline diagnostic annotations from actual output.
  --no-color            Disable ANSI colour output.

.lit-conf
---------
Each test directory may contain a ``.lit-conf`` file that supplies default
values for ``--define`` and ``--slang`` without requiring them on the command
line. This allows running the tests directly (without ctest) while still
resolving the correct binary and substitution paths.

Format: one directive per line; ``#`` lines and blank lines are ignored.

  define KEY=VALUE      Like --define KEY=VALUE.
  slang PATH            Like --slang PATH.

The special token ``${confdir}`` expands to the absolute path of the directory
containing the ``.lit-conf`` file, so paths relative to the test directory can
be written portably::

  define testdir=${confdir}
  define data=${confdir}/../../unittests/data

Command-line arguments always override ``.lit-conf`` values for the same key.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path


def _quote_arg(value: str) -> str:
    """Quote a shell argument for the current platform shell."""
    if os.name == "nt":
        return subprocess.list2cmdline([value])
    return shlex.quote(value)


# ---------------------------------------------------------------------------
# Color helpers
# ---------------------------------------------------------------------------

_USE_COLOR = True


def _color(code: str, text: str) -> str:
    if _USE_COLOR:
        return f"\033[{code}m{text}\033[0m"
    return text


def green(t: str) -> str:
    return _color("32", t)


def red(t: str) -> str:
    return _color("31", t)


def yellow(t: str) -> str:
    return _color("33", t)


# ---------------------------------------------------------------------------
# Directive parsing
# ---------------------------------------------------------------------------

# Matches any recognised directive comment.
_DIRECTIVE_RE = re.compile(
    r"^\s*//\s*"
    r"(RUN|CHECK-DIAGS|CHECK(?:-NEXT|-NOT|-DAG|-LABEL)?|XFAIL|REQUIRES)"
    r"\s*:\s*(.*?)\s*$"
)

_DIAG_ANNOTATION_RE = re.compile(r"^//[ \t]*\^+(?:\s+.*?)?\s*$")


@dataclass
class CheckDirective:
    kind: str  # CHECK / CHECK-NEXT / CHECK-NOT / CHECK-DAG / CHECK-LABEL
    pattern: str
    lineno: int


@dataclass
class ParsedTest:
    path: Path
    run_lines: list[str] = field(default_factory=list)
    check_directives: list[CheckDirective] = field(default_factory=list)
    diag_file: str | None = None
    diag_lines: set[int] = field(default_factory=set)
    xfail: bool = False
    requires: list[str] = field(default_factory=list)


def parse_test_file(path: Path) -> ParsedTest:
    """Extract directives from a test file."""
    result = ParsedTest(path=path)
    with path.open(encoding="utf-8", errors="replace") as fh:
        for lineno, raw_line in enumerate(fh, start=1):
            if _DIAG_ANNOTATION_RE.match(raw_line):
                result.diag_lines.add(lineno)
                continue

            m = _DIRECTIVE_RE.match(raw_line)
            if not m:
                continue
            kind, body = m.group(1), m.group(2)
            if kind == "RUN":
                result.run_lines.append(body)
            elif kind == "CHECK-DIAGS":
                if result.diag_file is not None:
                    raise ValueError(
                        f"{path}:{lineno}: multiple CHECK-DIAGS directives"
                    )
                result.diag_file = body
            elif kind == "XFAIL":
                result.xfail = True
            elif kind == "REQUIRES":
                result.requires.extend(r.strip() for r in body.split(","))
            else:
                result.check_directives.append(CheckDirective(kind, body, lineno))
    return result


# ---------------------------------------------------------------------------
# Substitution expansion
# ---------------------------------------------------------------------------


def expand_substitutions(
    command: str,
    *,
    source_path: Path,
    tmp_file: Path,
    tmp_dir: Path,
    slang_path: str,
    slang_is_cmdline: bool,
    user_defines: dict[str, str] | None = None,
) -> str:
    """Replace %s, %t, %T, %slang, and user-defined %KEY substitutions in a RUN-line command."""
    # Apply user-defined substitutions before the built-in ones so that user
    # values cannot accidentally match built-in tokens like %s or %t.
    if user_defines:
        for key, value in user_defines.items():
            command = command.replace(f"%{key}", _quote_arg(value))
    command = command.replace(
        "%slang", slang_path if slang_is_cmdline else _quote_arg(slang_path)
    )
    command = command.replace("%s", _quote_arg(str(source_path)))
    command = command.replace("%t", _quote_arg(str(tmp_file)))
    command = command.replace("%T", _quote_arg(str(tmp_dir)))
    return command


def expand_substitution_value(
    value: str,
    *,
    source_path: Path,
    tmp_file: Path,
    tmp_dir: Path,
    slang_path: str,
    user_defines: dict[str, str] | None = None,
) -> str:
    """Expand substitutions without shell quoting, for directive values."""
    if user_defines:
        for key, replacement in user_defines.items():
            value = value.replace(f"%{key}", replacement)
    value = value.replace("%slang", slang_path)
    value = value.replace("%s", str(source_path))
    value = value.replace("%t", str(tmp_file))
    value = value.replace("%T", str(tmp_dir))
    return value


# ---------------------------------------------------------------------------
# FileCheck-style output verification
# ---------------------------------------------------------------------------

# Matches {{...}} regex escapes inside CHECK patterns.
_BRACES_RE = re.compile(r"\{\{(.*?)\}\}")


def _compile_pattern(pattern: str) -> re.Pattern:
    """Compile a CHECK pattern to a regex.

    Text outside ``{{...}}`` is matched literally (as a plain substring).
    Text inside ``{{...}}`` is treated as a raw regular expression.
    """
    parts: list[str] = []
    last = 0
    for m in _BRACES_RE.finditer(pattern):
        parts.append(re.escape(pattern[last : m.start()]))
        parts.append(m.group(1))  # raw regex
        last = m.end()
    parts.append(re.escape(pattern[last:]))
    return re.compile("".join(parts))


class CheckError(Exception):
    """Raised when a CHECK directive is violated."""

    def __init__(
        self,
        directive: CheckDirective,
        message: str,
        context: str = "",
        region_start: int = 0,
        region_end: int | None = None,
    ):
        self.directive = directive
        self.message = message
        self.context = context
        self.region_start = region_start
        self.region_end = region_end
        super().__init__(directive, message, context, region_start, region_end)


def run_checks(output: str, directives: list[CheckDirective]) -> None:
    """Verify *output* against the list of CHECK directives.

    Raises CheckError on the first failure.
    """
    lines = output.splitlines()

    # Partition directives into sequential groups. A CHECK-DAG block is a
    # maximal run of consecutive CHECK-DAG directives.
    # CHECK-NOT directives are accumulated and validated against the window
    # between the surrounding positive checks.

    pos = 0  # current scan position in *lines*
    i = 0  # index into directives

    # region_end caps all forward scans (CHECK, CHECK-DAG, CHECK-NOT) to the
    # current CHECK-LABEL region. This prevents a pattern from matching in a
    # later labelled section.
    region_end = len(lines)
    # region_start tracks the first line of the current label region (inclusive).
    region_start = 0

    def _next_label_bound(from_pos: int, from_directive: int) -> int:
        """Return the line index where the next CHECK-LABEL after *from_directive*
        first matches, searching from *from_pos*. Returns len(lines) when there
        is no further CHECK-LABEL or its pattern doesn't match."""
        for j in range(from_directive, len(directives)):
            if directives[j].kind == "CHECK-LABEL":
                try:
                    pat = _compile_pattern(directives[j].pattern)
                except re.error:
                    break
                for lno in range(from_pos, len(lines)):
                    if pat.search(lines[lno]):
                        return lno
                break
        return len(lines)

    # Collect pending CHECK-NOT patterns that must not match until the next
    # positive check (or end-of-directives).
    pending_not: list[CheckDirective] = []

    def _assert_not_in_window(start: int, end: int) -> None:
        """Fail if any CHECK-NOT pattern matches in lines[start:end]."""
        for nd in pending_not:
            try:
                pat = _compile_pattern(nd.pattern)
            except re.error as exc:
                raise CheckError(
                    nd,
                    f"bad regex in CHECK-NOT {{{{...}}}}: {exc}",
                    region_start=region_start,
                    region_end=region_end,
                ) from exc
            for ln in lines[start:end]:
                if pat.search(ln):
                    raise CheckError(
                        nd,
                        "CHECK-NOT pattern unexpectedly matched",
                        context=f"  matched line: {ln!r}\n  pattern:      {nd.pattern!r}",
                        region_start=region_start,
                        region_end=region_end,
                    )

    not_window_start = 0

    while i < len(directives):
        d = directives[i]

        if d.kind == "CHECK-NOT":
            pending_not.append(d)
            i += 1
            continue

        # --- Flush pending NOT checks against [not_window_start, pos) ---
        _assert_not_in_window(not_window_start, pos)
        pending_not.clear()
        not_window_start = pos

        if d.kind == "CHECK-DAG":
            # Collect the whole DAG group.
            dag_group: list[CheckDirective] = []
            while i < len(directives) and directives[i].kind == "CHECK-DAG":
                dag_group.append(directives[i])
                i += 1

            # Each pattern in the group must match at least once in lines[pos:region_end].
            matched_lines: set[int] = set()
            for dd in dag_group:
                try:
                    pat = _compile_pattern(dd.pattern)
                except re.error as exc:
                    raise CheckError(
                        dd,
                        f"bad regex in CHECK-DAG {{{{...}}}}: {exc}",
                        region_start=region_start,
                        region_end=region_end,
                    ) from exc
                found = False
                for lno, ln in enumerate(lines[pos:region_end], start=pos):
                    if pat.search(ln):
                        matched_lines.add(lno)
                        found = True
                        break
                if not found:
                    raise CheckError(
                        dd,
                        "CHECK-DAG pattern not found in output",
                        context=f"  pattern: {dd.pattern!r}",
                        region_start=region_start,
                        region_end=region_end,
                    )
            # Advance pos past the last matched line.
            if matched_lines:
                pos = max(matched_lines) + 1
            continue

        if d.kind == "CHECK-LABEL":
            try:
                pat = _compile_pattern(d.pattern)
            except re.error as exc:
                raise CheckError(
                    d,
                    f"bad regex in CHECK-LABEL {{{{...}}}}: {exc}",
                    region_start=region_start,
                    region_end=region_end,
                ) from exc
            found = False
            for lno in range(pos, len(lines)):
                if pat.search(lines[lno]):
                    region_start = (
                        lno  # include the matched label line in the new region
                    )
                    pos = lno + 1
                    found = True
                    break
            if not found:
                raise CheckError(
                    d,
                    "CHECK-LABEL pattern not found in output",
                    context=f"  pattern: {d.pattern!r}",
                    region_start=region_start,
                    region_end=region_end,
                )
            i += 1
            # Cap subsequent scans to before the next label's match position.
            region_end = _next_label_bound(pos, i)
            continue

        if d.kind == "CHECK-NEXT":
            # Must match on exactly the next line (pos).
            if pos >= len(lines):
                raise CheckError(
                    d,
                    "CHECK-NEXT reached end of output",
                    context=f"  pattern: {d.pattern!r}",
                    region_start=region_start,
                    region_end=region_end,
                )
            try:
                pat = _compile_pattern(d.pattern)
            except re.error as exc:
                raise CheckError(
                    d,
                    f"bad regex in CHECK-NEXT {{{{...}}}}: {exc}",
                    region_start=region_start,
                    region_end=region_end,
                ) from exc
            if not pat.search(lines[pos]):
                raise CheckError(
                    d,
                    "CHECK-NEXT pattern did not match the next line",
                    context=(
                        f"  pattern:    {d.pattern!r}\n  next line:  {lines[pos]!r}"
                    ),
                    region_start=region_start,
                    region_end=region_end,
                )
            pos += 1
            i += 1
            continue

        # Plain CHECK
        try:
            pat = _compile_pattern(d.pattern)
        except re.error as exc:
            raise CheckError(
                d,
                f"bad regex in CHECK {{{{...}}}}: {exc}",
                region_start=region_start,
                region_end=region_end,
            ) from exc
        found = False
        for lno in range(pos, region_end):
            if pat.search(lines[lno]):
                pos = lno + 1
                found = True
                break
        if not found:
            raise CheckError(
                d,
                "CHECK pattern not found in output",
                context=f"  pattern: {d.pattern!r}",
                region_start=region_start,
                region_end=region_end,
            )
        i += 1

    # Final NOT check for the tail of the current region.
    _assert_not_in_window(not_window_start, region_end)


# ---------------------------------------------------------------------------
# Inline diagnostic verification
# ---------------------------------------------------------------------------


@dataclass(frozen=True, order=True)
class DiagSegment:
    line: int
    start_column: int
    end_column: int


@dataclass
class ActualDiagnostic:
    code: str
    message: str
    segments: set[DiagSegment]


class DiagCheckError(Exception):
    """Raised when CHECK-DIAGS annotations don't match JSON diagnostics."""


def _same_file(reported: str, test_path: Path) -> bool:
    resolved_test = test_path.resolve()
    try:
        if Path(reported).resolve() == resolved_test:
            return True
    except OSError:
        pass

    # WASI reports host absolute paths without the leading slash. Resolving such
    # a path on the host incorrectly treats it as relative to the current working
    # directory, so also compare it against the root-relative spelling.
    if not Path(reported).is_absolute():
        reported_norm = os.path.normcase(os.path.normpath(reported))
        test_norm = os.path.normcase(os.path.normpath(str(resolved_test)))
        return reported_norm == test_norm.lstrip("/\\")

    return False


def _parse_location(location: str) -> tuple[str, int, int] | None:
    try:
        filename, line, column = location.rsplit(":", 2)
        return filename, int(line), int(column)
    except (AttributeError, TypeError, ValueError):
        return None


def _range_segments(
    start: dict,
    end: dict,
    *,
    test_path: Path,
    source_lines: list[str],
    diag_lines: set[int],
) -> set[DiagSegment]:
    if not _same_file(start.get("file", ""), test_path):
        return set()
    if not _same_file(end.get("file", ""), test_path):
        return set()

    try:
        start_line = int(start["line"])
        start_column = int(start["column"])
        end_line = int(end["line"])
        end_column = int(end["column"])
    except (KeyError, TypeError, ValueError):
        return set()

    if (end_line, end_column) < (start_line, start_column):
        return set()

    result: set[DiagSegment] = set()
    for lineno in range(start_line, end_line + 1):
        if lineno in diag_lines or not 1 <= lineno <= len(source_lines):
            continue

        line_length = len(source_lines[lineno - 1])
        segment_start = start_column if lineno == start_line else 1
        segment_end = end_column if lineno == end_line else line_length + 1

        # Multiline ranges include leading indentation and trailing whitespace on
        # continuation lines. Squiggle only the visible source text so annotations
        # remain useful and can physically align after the leading `//`.
        line_text = source_lines[lineno - 1]
        if segment_start == 1:
            first_text_column = len(line_text) - len(line_text.lstrip()) + 1
            segment_start = max(segment_start, first_text_column)
        if segment_end == line_length + 1:
            segment_end = min(segment_end, len(line_text.rstrip()) + 1)

        segment_start = max(1, min(segment_start, line_length + 1))
        segment_end = max(1, min(segment_end, line_length + 1))
        if segment_end <= segment_start:
            if start_line == end_line and start_column == end_column:
                segment_end = segment_start + 1
            else:
                continue

        result.add(DiagSegment(lineno, segment_start, segment_end))
    return result


def _load_json_diagnostics(diag_path: Path) -> list[dict]:
    try:
        with diag_path.open(encoding="utf-8") as fh:
            json_diags = json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        raise DiagCheckError(
            f"unable to read CHECK-DIAGS file {diag_path}: {exc}"
        ) from exc

    if not isinstance(json_diags, list):
        raise DiagCheckError(f"CHECK-DIAGS file {diag_path} must contain a JSON array")

    return [item for item in json_diags if isinstance(item, dict)]


def _collect_actual_groups(
    parsed: ParsedTest,
    json_diags: list[dict],
    source_lines: list[str],
    diag_lines: set[int],
) -> list[list[ActualDiagnostic]]:
    def collect_actual(item: dict, group: list[ActualDiagnostic]) -> None:
        location = _parse_location(item.get("location", ""))
        if location and _same_file(location[0], parsed.path):
            segments: set[DiagSegment] = set()
            for source_range in item.get("ranges", []):
                if isinstance(source_range, dict):
                    segments.update(
                        _range_segments(
                            source_range.get("start", {}),
                            source_range.get("end", {}),
                            test_path=parsed.path,
                            source_lines=source_lines,
                            diag_lines=diag_lines,
                        )
                    )

            if not segments:
                _, line, column = location
                segments.add(DiagSegment(line, column, column + 1))

            group.append(
                ActualDiagnostic(
                    code=str(item.get("code", "")),
                    message=str(item.get("message", "")),
                    segments=segments,
                )
            )

        for note in item.get("notes", []):
            if isinstance(note, dict):
                collect_actual(note, group)

    actual_groups: list[list[ActualDiagnostic]] = []
    for item in json_diags:
        group: list[ActualDiagnostic] = []
        collect_actual(item, group)
        if group:
            actual_groups.append(group)
    return actual_groups


def _diag_reference(
    diagnostic: ActualDiagnostic,
    source_lines: list[str],
    *,
    include_args: bool,
) -> str:
    if not include_args:
        return diagnostic.code

    args: list[str] = []
    quoted_arg = re.search(r"(?<![A-Za-z0-9_$])'([^']+)'", diagnostic.message)
    message_without_quotes = diagnostic.message
    if quoted_arg:
        args.append(quoted_arg.group(1))
        message_without_quotes = (
            diagnostic.message[: quoted_arg.start()]
            + diagnostic.message[quoted_arg.end() :]
        )

    number_arg = re.search(
        r"(?<![A-Za-z0-9_$'])-?\d+(?![A-Za-z0-9_$'])", message_without_quotes
    )
    if number_arg:
        args.append(number_arg.group())

    if not args:
        segment = min(diagnostic.segments)
        source_line = source_lines[segment.line - 1]
        source_arg = source_line[segment.start_column - 1 : segment.end_column - 1]
        source_arg = source_arg.strip()
        if source_arg and len(source_arg) <= 32:
            args.append(source_arg)

    if not args:
        return diagnostic.code
    return f"{diagnostic.code}({', '.join(args)})"


def _format_diag_annotation(segment: DiagSegment) -> str:
    if segment.start_column < 3:
        raise DiagCheckError(
            "cannot generate an inline diagnostic annotation for a range before "
            f"column 3 ({segment.line}:{segment.start_column})"
        )
    return (
        "//"
        + " " * (segment.start_column - 3)
        + "^" * (segment.end_column - segment.start_column)
    )


def _generate_diag_expectations(parsed: ParsedTest, diag_path: Path) -> str:
    """Generate the test file with canonical annotations from JSON diagnostics."""
    json_diags = _load_json_diagnostics(diag_path)
    old_text = parsed.path.read_text(encoding="utf-8", errors="replace")
    source_lines = old_text.splitlines()
    actual_groups = _collect_actual_groups(
        parsed, json_diags, source_lines, parsed.diag_lines
    )

    annotations_by_line: dict[int, list[str]] = {}
    for group in actual_groups:
        reference = _diag_reference(group[0], source_lines, include_args=len(group) > 1)

        for diagnostic_index, diagnostic in enumerate(group):
            for index, segment in enumerate(sorted(diagnostic.segments)):
                annotation = _format_diag_annotation(segment)
                if index == 0:
                    annotation += f" {diagnostic.code} {diagnostic.message}"
                if diagnostic_index > 0 or index > 0:
                    annotation += f" - for {reference}"
                annotations_by_line.setdefault(segment.line, []).append(annotation)

    output_lines: list[str] = []
    for lineno, line in enumerate(source_lines, start=1):
        if lineno in parsed.diag_lines:
            continue
        output_lines.append(line)
        output_lines.extend(annotations_by_line.get(lineno, []))

    return "\n".join(output_lines) + ("\n" if old_text.endswith("\n") else "")


def run_diag_checks(parsed: ParsedTest, diag_path: Path) -> None:
    """Check diagnostic annotations against the canonically generated file."""
    old_text = parsed.path.read_text(encoding="utf-8", errors="replace")
    new_text = _generate_diag_expectations(parsed, diag_path)
    if new_text == old_text:
        return

    diff = difflib.unified_diff(
        old_text.splitlines(),
        new_text.splitlines(),
        fromfile=str(parsed.path),
        tofile=f"{parsed.path} (generated)",
        lineterm="",
    )
    raise DiagCheckError(
        "diagnostic annotations do not match; rerun with --update-diags\n"
        + "\n".join(diff)
    )


def update_diags(parsed: ParsedTest, diag_path: Path) -> bool:
    """Rewrite inline squiggle annotations to match JSON diagnostics."""
    old_text = parsed.path.read_text(encoding="utf-8", errors="replace")
    new_text = _generate_diag_expectations(parsed, diag_path)
    if new_text == old_text:
        return False

    parsed.path.write_text(new_text, encoding="utf-8")
    return True


# ---------------------------------------------------------------------------
# Single test execution
# ---------------------------------------------------------------------------


@dataclass
class TestResult:
    path: Path
    status: str  # PASS / FAIL / XFAIL / XPASS / SKIP
    elapsed: float
    message: str = ""
    output: str = ""


def run_test(
    parsed: ParsedTest,
    *,
    slang_path: str,
    slang_is_cmdline: bool,
    tmp_dir: Path,
    verbose: bool,
    available_features: set[str],
    output_limit: int | None = 30,
    user_defines: dict[str, str] | None = None,
    should_update_diags: bool = False,
) -> TestResult:
    start = time.monotonic()

    # --- Requirements check ---------------------------------------------------
    for req in parsed.requires:
        if req not in available_features:
            return TestResult(
                path=parsed.path,
                status="SKIP",
                elapsed=time.monotonic() - start,
                message=f"requirement not met: {req!r}",
            )

    if not parsed.run_lines:
        return TestResult(
            path=parsed.path,
            status="SKIP",
            elapsed=time.monotonic() - start,
            message="no RUN directives found",
        )

    # --- Build substitution context ------------------------------------------
    tmp_file = tmp_dir / (parsed.path.stem + ".tmp")

    # --- Execute RUN commands -------------------------------------------------
    combined_output = ""
    for run_cmd in parsed.run_lines:
        ignore_exit = False
        if re.search(r"\|\|\s*true\s*$", run_cmd):
            # Keep tests portable across shells where `true` may not exist
            # (notably cmd.exe on Windows).
            run_cmd = re.sub(r"\s*\|\|\s*true\s*$", "", run_cmd)
            ignore_exit = True

        cmd = expand_substitutions(
            run_cmd,
            source_path=parsed.path.resolve(),
            tmp_file=tmp_file,
            tmp_dir=tmp_dir,
            slang_path=slang_path,
            slang_is_cmdline=slang_is_cmdline,
            user_defines=user_defines,
        )
        if os.name == "nt":
            # cmd.exe does not interpret single quotes as quoting characters;
            # they are passed literally to the child process.  Convert
            # 'arg' -> "arg" so that grouped arguments work on Windows.
            cmd = re.sub(
                r"'([^']*)'",
                lambda m: '"' + m.group(1).replace('"', '\\"') + '"',
                cmd,
            )
        if verbose:
            print(f"  $ {cmd}")
        try:
            proc = subprocess.run(
                cmd,
                shell=True,
                capture_output=True,
                text=True,
                timeout=60,
                check=False,
            )
        except subprocess.TimeoutExpired:
            elapsed = time.monotonic() - start
            msg = f"test timed out after 60 s\n  command: {cmd}"
            status = "XFAIL" if parsed.xfail else "FAIL"
            return TestResult(
                path=parsed.path, status=status, elapsed=elapsed, message=msg
            )

        combined_output += proc.stdout
        if proc.returncode != 0 and not ignore_exit:
            elapsed = time.monotonic() - start
            if parsed.xfail:
                return TestResult(
                    path=parsed.path,
                    status="XFAIL",
                    elapsed=elapsed,
                )
            msg = f"command exited with code {proc.returncode}\n  command: {cmd}"
            if proc.stderr:
                stderr_preview = "\n".join(
                    f"    {ln}" for ln in proc.stderr.splitlines()[:30]
                )
                msg += f"\n  stderr:\n{stderr_preview}"
            return TestResult(
                path=parsed.path,
                status="FAIL",
                elapsed=elapsed,
                message=msg,
                output=combined_output,
            )

    # --- Check inline diagnostic annotations ---------------------------------
    if parsed.diag_file is not None:
        diag_file = expand_substitution_value(
            parsed.diag_file,
            source_path=parsed.path.resolve(),
            tmp_file=tmp_file,
            tmp_dir=tmp_dir,
            slang_path=slang_path,
            user_defines=user_defines,
        )
        diag_path = Path(diag_file)
        try:
            if should_update_diags and update_diags(parsed, diag_path):
                result = run_test(
                    parse_test_file(parsed.path),
                    slang_path=slang_path,
                    slang_is_cmdline=slang_is_cmdline,
                    tmp_dir=tmp_dir,
                    verbose=verbose,
                    available_features=available_features,
                    output_limit=output_limit,
                    user_defines=user_defines,
                )
                result.elapsed = time.monotonic() - start
                if result.status == "PASS":
                    result.message = "updated diagnostic expectations"
                return result
            run_diag_checks(parsed, diag_path)
        except DiagCheckError as exc:
            elapsed = time.monotonic() - start
            status = "XFAIL" if parsed.xfail else "FAIL"
            return TestResult(
                path=parsed.path,
                status=status,
                elapsed=elapsed,
                message=str(exc),
                output=combined_output,
            )

    # --- Run CHECK directives -------------------------------------------------
    try:
        run_checks(combined_output, parsed.check_directives)
    except CheckError as exc:
        elapsed = time.monotonic() - start
        lines = [exc.message]
        if exc.context:
            lines.append(exc.context)
        lines.append(f"  directive at: {parsed.path}:{exc.directive.lineno}")
        output_lines = combined_output.splitlines()
        r_start = exc.region_start
        r_end = exc.region_end if exc.region_end is not None else len(output_lines)
        region_lines = output_lines[r_start:r_end]
        truncated = output_limit is not None and len(region_lines) > output_limit
        preview_lines = (
            region_lines[:output_limit] if output_limit is not None else region_lines
        )
        failing_output_preview = "\n".join(f"    {ln}" for ln in preview_lines)
        if region_lines:
            if r_start > 0 or r_end < len(output_lines):
                label = (
                    f"output region [{r_start + 1}:{r_end}] (first {output_limit} lines)"
                    if truncated
                    else f"output region [{r_start + 1}:{r_end}]"
                )
            else:
                label = (
                    f"output (first {output_limit} lines)" if truncated else "output"
                )
            lines.append(f"  {label}:\n{failing_output_preview}")
        msg = "\n".join(lines)
        status = "XFAIL" if parsed.xfail else "FAIL"
        return TestResult(
            path=parsed.path,
            status=status,
            elapsed=elapsed,
            message=msg,
            output=combined_output,
        )

    elapsed = time.monotonic() - start
    if parsed.xfail:
        # Test was expected to fail but passed.
        return TestResult(path=parsed.path, status="XPASS", elapsed=elapsed)
    return TestResult(path=parsed.path, status="PASS", elapsed=elapsed)


# ---------------------------------------------------------------------------
# Test discovery
# ---------------------------------------------------------------------------

_TEST_EXTENSIONS = {".sv", ".v", ".lit"}


def discover_tests(paths: list[Path], filter_re: re.Pattern | None) -> list[Path]:
    """Return all test files reachable from *paths* (files or directories)."""
    result: list[Path] = []
    for p in paths:
        if p.is_file():
            if filter_re is None or filter_re.search(str(p)):
                result.append(p)
        elif p.is_dir():
            for root, _dirs, files in os.walk(p):
                for name in sorted(files):
                    fp = Path(root) / name
                    if fp.suffix in _TEST_EXTENSIONS and (
                        filter_re is None or filter_re.search(str(fp))
                    ):
                        result.append(fp)
        else:
            print(f"warning: {p} does not exist, skipping", file=sys.stderr)
    return result


# ---------------------------------------------------------------------------
# slang binary resolution
# ---------------------------------------------------------------------------

_SCRIPT_DIR = Path(__file__).resolve().parent


def find_slang(hint: str | None = None) -> str:
    """Return a path to the slang binary, or raise SystemExit."""
    if hint:
        # Allow passing a full command line, for example a wasm launcher plus
        # path to binary.
        if any(ch.isspace() for ch in hint.strip()):
            return hint
        if shutil.which(hint):
            return hint
        if Path(hint).is_file():
            return str(Path(hint).resolve())
        print(f"error: specified slang binary not found: {hint!r}", file=sys.stderr)
        sys.exit(1)

    # Check PATH first.
    found = shutil.which("slang")
    if found:
        return found

    # Scan every immediate subdirectory of <repo>/build/ and pick the one
    # whose bin/slang binary has the most recent modification time.
    repo_root = _SCRIPT_DIR.parent
    build_root = repo_root / "build"
    best: tuple[float, Path] | None = None
    if build_root.is_dir():
        for entry in build_root.iterdir():
            for candidate_name in ("slang", "slang.exe"):
                candidate = entry / "bin" / candidate_name
                if candidate.is_file():
                    mtime = candidate.stat().st_mtime
                    if best is None or mtime > best[0]:
                        best = (mtime, candidate)
    if best is not None:
        return str(best[1])

    print(
        "error: slang binary not found. Use --slang to specify its path.",
        file=sys.stderr,
    )
    sys.exit(1)


# ---------------------------------------------------------------------------
# .lit-conf loader
# ---------------------------------------------------------------------------


def load_lit_conf(directory: Path) -> dict:
    """Load settings from an optional ``.lit-conf`` file in *directory*.

    Returns a dict with optional keys ``"defines"`` (list of ``KEY=VALUE``
    strings) and ``"slang"`` (str path).
    """
    conf_path = directory / ".lit-conf"
    if not conf_path.is_file():
        return {}

    conf_dir = str(directory.resolve())
    result: dict = {"defines": []}
    with conf_path.open() as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            # Expand ${confdir} to the directory containing the .lit-conf file.
            line = line.replace("${confdir}", conf_dir)
            if line.startswith("define "):
                value = line[len("define ") :].strip()
                # Normalise any absolute path that may contain .. segments.
                if "=" in value:
                    k, _, v = value.partition("=")
                    if os.path.isabs(v):
                        v = os.path.normpath(v)
                    value = f"{k}={v}"
                result["defines"].append(value)
            elif line.startswith("slang "):
                slang_val = line[len("slang ") :].strip()
                if os.path.isabs(slang_val):
                    slang_val = os.path.normpath(slang_val)
                result["slang"] = slang_val
            else:
                print(
                    f"warning: {conf_path}:{lineno}: unrecognised directive {line!r}",
                    file=sys.stderr,
                )
    return result


def maybe_wrap_wasm_launcher(slang_bin: str) -> tuple[str, bool]:
    """Return (command, is_cmdline) and auto-wrap wasm binaries via wasmtime."""
    p = Path(slang_bin)
    if not p.is_file():
        return slang_bin, False

    try:
        with p.open("rb") as fh:
            magic = fh.read(4)
    except OSError:
        return slang_bin, False

    if magic != b"\0asm":
        return slang_bin, False

    wasmtime = shutil.which("wasmtime")
    if not wasmtime:
        return slang_bin, False

    tests_dir = (_SCRIPT_DIR.parent / "tests").resolve()
    cmd = " ".join(
        [
            _quote_arg(wasmtime),
            "run",
            "--dir=/",
            f"--dir={_quote_arg(str(tests_dir))}::tests",
            _quote_arg(str(p.resolve())),
        ]
    )
    return cmd, True


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------


def usable_cpu_count() -> int:
    """Return the number of CPUs this process may actually run on.

    os.cpu_count() reports the CPUs of the machine and ignores any restriction
    placed on the process, so a run pinned to a couple of cores would still
    start a job per CPU of the host.
    """
    process_cpu_count = getattr(os, "process_cpu_count", None)
    if process_cpu_count is not None:  # Python 3.13+
        return process_cpu_count() or 1
    if hasattr(os, "sched_getaffinity"):
        return len(os.sched_getaffinity(0)) or 1
    return os.cpu_count() or 1


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    _default_jobs = usable_cpu_count()

    p = argparse.ArgumentParser(
        description=__doc__ or "",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("paths", nargs="+", metavar="PATH", help="Test files or directories")
    p.add_argument("--slang", metavar="PATH", help="Path to the slang binary")
    p.add_argument("-v", "--verbose", action="store_true", help="Show each RUN command")
    p.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=_default_jobs,
        metavar="N",
        help=f"Number of parallel test jobs (default: {_default_jobs})",
    )
    p.add_argument(
        "--filter", metavar="REGEX", help="Only run tests whose path matches REGEX"
    )
    p.add_argument(
        "--update-diags",
        action="store_true",
        help="Rewrite inline diagnostic annotations from actual output",
    )
    p.add_argument("--no-color", action="store_true", help="Disable ANSI colour output")
    p.add_argument(
        "--define",
        metavar="KEY=VALUE",
        action="append",
        default=[],
        help="Define a custom %%KEY substitution for use in RUN lines (repeatable)",
    )
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    global _USE_COLOR

    args = parse_args(argv)

    if args.no_color or not sys.stdout.isatty():
        _USE_COLOR = False

    # Load .lit-conf files from each input directory (or a file's parent
    # directory). These provide default values for --define and --slang that
    # are overridden by explicit command-line arguments.
    conf_defines: dict[str, str] = {}
    conf_slang: str | None = None
    seen_conf_dirs: set[Path] = set()
    for path_str in args.paths:
        p = Path(path_str)
        dir_p = p if p.is_dir() else p.parent
        dir_p = dir_p.resolve()
        if dir_p in seen_conf_dirs:
            continue
        seen_conf_dirs.add(dir_p)
        conf = load_lit_conf(dir_p)
        for defn in conf.get("defines", []):
            if "=" in defn:
                k, _, v = defn.partition("=")
                conf_defines.setdefault(k.strip(), v)
        if "slang" in conf and conf_slang is None:
            conf_slang = conf["slang"]

    slang_bin = find_slang(args.slang or conf_slang)
    slang_cmd, slang_is_cmdline = maybe_wrap_wasm_launcher(slang_bin)

    # Parse --define KEY=VALUE arguments into a substitution dict.
    # Conf-file defines provide defaults; CLI --define overrides them.
    user_defines: dict[str, str] = dict(conf_defines)
    for defn in args.define:
        if "=" not in defn:
            print(
                f"error: --define {defn!r}: expected KEY=VALUE format", file=sys.stderr
            )
            return 1
        k, _, v = defn.partition("=")
        user_defines[k.strip()] = v

    filter_re: re.Pattern | None = None
    if args.filter:
        try:
            filter_re = re.compile(args.filter)
        except re.error as exc:
            print(f"error: invalid --filter regex: {exc}", file=sys.stderr)
            return 1

    test_paths = discover_tests([Path(p) for p in args.paths], filter_re)
    if not test_paths:
        print("warning: no test files found", file=sys.stderr)
        return 0

    parsed_tests = [parse_test_file(p) for p in test_paths]

    # Determine which features are available.
    available_features: set[str] = set()
    # Check if the binary supports LLVM flags.
    try:
        help_out = subprocess.run(
            [slang_bin, "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=10,
            check=False,
        ).stdout
        if "--emit-ir" in help_out:
            available_features.add("llvm")
    except (OSError, subprocess.SubprocessError):
        pass

    # Each --define KEY=VALUE also registers KEY as an available feature so
    # that tests can guard themselves with `// REQUIRES: KEY` and be skipped
    # gracefully when the define is absent (e.g. when running outside ctest).
    available_features.update(user_defines.keys())

    results: list[TestResult] = []
    total = len(parsed_tests)
    width = len(str(total))

    print(f"Running {total} test{'s' if total != 1 else ''} with {slang_cmd}\n")

    with tempfile.TemporaryDirectory(prefix="slang_lit_") as tmpdir:
        tmp_dir = Path(tmpdir)

        def _run(pt: ParsedTest) -> TestResult:
            return run_test(
                pt,
                slang_path=slang_cmd,
                slang_is_cmdline=slang_is_cmdline,
                tmp_dir=tmp_dir,
                verbose=args.verbose,
                available_features=available_features,
                output_limit=None if total == 1 else 30,
                user_defines=user_defines or None,
                should_update_diags=args.update_diags,
            )

        if args.jobs > 1:
            with ThreadPoolExecutor(max_workers=args.jobs) as ex:
                future_map = {ex.submit(_run, pt): pt for pt in parsed_tests}
                for fut in as_completed(future_map):
                    r = fut.result()
                    results.append(r)
                    _print_result(r, total, len(results), width)
        else:
            for pt in parsed_tests:
                r = run_test(
                    pt,
                    slang_path=slang_cmd,
                    slang_is_cmdline=slang_is_cmdline,
                    tmp_dir=tmp_dir,
                    verbose=args.verbose,
                    available_features=available_features,
                    output_limit=None if total == 1 else 30,
                    user_defines=user_defines or None,
                    should_update_diags=args.update_diags,
                )
                results.append(r)
                _print_result(r, total, len(results), width)

    return _summarise(results)


def _print_result(r: TestResult, total: int, done: int, width: int) -> None:
    icon = {
        "PASS": green("PASS"),
        "FAIL": red("FAIL"),
        "XFAIL": yellow("XFAIL"),
        "XPASS": yellow("XPASS"),
        "SKIP": "SKIP",
    }.get(r.status, r.status)

    rel = r.path.name
    print(f"[{done:>{width}}/{total}] {icon}  {rel}  ({r.elapsed:.2f}s)")

    if r.status == "PASS" and r.message:
        print(f"       {r.message}")
    elif r.status in ("FAIL", "XPASS") and r.message:
        for line in r.message.splitlines():
            print(f"       {line}")
        print()


def _summarise(results: list[TestResult]) -> int:
    counts: dict[str, int] = {}
    for r in results:
        counts[r.status] = counts.get(r.status, 0) + 1

    print()
    parts = []
    if counts.get("PASS"):
        parts.append(green(f"{counts['PASS']} passed"))
    if counts.get("FAIL"):
        parts.append(red(f"{counts['FAIL']} failed"))
    if counts.get("XFAIL"):
        parts.append(yellow(f"{counts['XFAIL']} expected failures"))
    if counts.get("XPASS"):
        parts.append(yellow(f"{counts['XPASS']} unexpected passes"))
    if counts.get("SKIP"):
        parts.append(f"{counts['SKIP']} skipped")

    print("Results: " + ", ".join(parts))

    failed = counts.get("FAIL", 0) + counts.get("XPASS", 0)
    return 1 if failed > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
