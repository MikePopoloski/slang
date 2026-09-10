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
def pyright_output(example_py: Path, checker_command) -> dict[str, Any]:
    """Run pyright once and return its JSON output."""
    result = subprocess.run(
        [
            *checker_command("pyright"),
            "--outputjson",
            "--pythonpath",
            sys.executable,
            str(example_py),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if not result.stdout.strip():
        pytest.fail(
            "pyright did not produce JSON output "
            f"(exit status {result.returncode}): {result.stderr}"
        )

    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as error:
        pytest.fail(f"Could not parse pyright output as JSON: {error}\n{result.stdout}")


def test_submodule_members_are_typed(
    pyright_output: dict[str, Any],
    submodule_probe_members: dict[str, str],
    format_diagnostics,
):
    """Pyright should resolve every probed member to a concrete type."""
    diagnostics = pyright_output.get("generalDiagnostics", [])
    errors = [
        diagnostic
        for diagnostic in diagnostics
        if diagnostic.get("severity") == "error"
    ]
    assert not errors, "pyright reported errors:\n" + format_diagnostics(errors)

    reveals = [
        diagnostic
        for diagnostic in diagnostics
        if diagnostic.get("severity") == "information"
        and str(diagnostic.get("message", "")).startswith("Type of ")
    ]
    expected_reveals = len(submodule_probe_members) * 2
    assert len(reveals) == expected_reveals, (
        f"Expected {expected_reveals} pyright reveal_type diagnostics, "
        f"got {len(reveals)}:\n{format_diagnostics(reveals)}"
    )

    unknown = [
        diagnostic for diagnostic in reveals if "Unknown" in diagnostic["message"]
    ]
    assert not unknown, (
        "pyright could not resolve these members:\n" + format_diagnostics(unknown)
    )
