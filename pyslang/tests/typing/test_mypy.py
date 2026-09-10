# SPDX-FileCopyrightText: Benjamin Davis
# SPDX-License-Identifier: MIT

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


@pytest.fixture(scope="module")
def mypy_output(example_py: Path, checker_command) -> list[dict[str, Any]]:
    """Run mypy once and return its line-delimited JSON diagnostics."""
    result = subprocess.run(
        [
            *checker_command("mypy"),
            "--no-incremental",
            "--no-error-summary",
            "--output=json",
            "--python-executable",
            sys.executable,
            str(example_py),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if not result.stdout.strip():
        pytest.fail(
            "mypy did not produce JSON output "
            f"(exit status {result.returncode}): {result.stderr}"
        )

    try:
        return [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    except json.JSONDecodeError as error:
        pytest.fail(f"Could not parse mypy output as JSON: {error}\n{result.stdout}")


def test_submodule_members_are_typed_with_mypy(
    mypy_output: list[dict[str, Any]],
    submodule_probe_members: dict[str, str],
    format_diagnostics,
):
    """Mypy should resolve every probed member to a concrete type."""
    errors = [
        diagnostic
        for diagnostic in mypy_output
        if diagnostic.get("severity") == "error"
    ]
    assert not errors, "mypy reported errors:\n" + format_diagnostics(errors)

    reveals = [
        diagnostic
        for diagnostic in mypy_output
        if diagnostic.get("severity") == "note"
        and str(diagnostic.get("message", "")).startswith("Revealed type is ")
    ]
    expected_reveals = len(submodule_probe_members) * 2
    assert len(reveals) == expected_reveals, (
        f"Expected {expected_reveals} mypy reveal_type diagnostics, "
        f"got {len(reveals)}:\n{format_diagnostics(reveals)}"
    )

    unknown = [diagnostic for diagnostic in reveals if "Any" in diagnostic["message"]]
    assert not unknown, "mypy could not resolve these members:\n" + format_diagnostics(
        unknown
    )
