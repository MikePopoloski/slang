# SPDX-FileCopyrightText: Benjamin Davis
# SPDX-License-Identifier: MIT

from __future__ import annotations

import importlib.util
import shutil
import sys
from pathlib import Path

import pytest

# Sub-modules publicly exposed by pyslang/pyslang/__init__.py.
SUBMODULES = ("ast", "syntax", "parsing", "analysis", "driver")

# A representative member of each sub-module used to probe the stubs.
SUBMODULE_PROBE_MEMBERS = {
    "ast": "Compilation",
    "syntax": "SyntaxTree",
    "parsing": "LexerOptions",
    "analysis": "AnalysisManager",
    "driver": "Driver",
}


@pytest.fixture(scope="session")
def submodules() -> tuple[str, ...]:
    return SUBMODULES


@pytest.fixture(scope="session")
def submodule_probe_members() -> dict[str, str]:
    return SUBMODULE_PROBE_MEMBERS


@pytest.fixture(scope="module")
def example_py(
    tmp_path_factory: pytest.TempPathFactory,
    submodules: tuple[str, ...],
    submodule_probe_members: dict[str, str],
) -> Path:
    """Write one probe containing all supported forms of sub-module import."""
    lines = [
        "import pyslang",
        "",
        "",
        "def top_level_import() -> None:",
    ]
    lines.extend(
        f"    reveal_type(pyslang.{module}.{member})"
        for module, member in submodule_probe_members.items()
    )
    lines.extend(["", ""])

    lines.extend(["def import_from() -> None:"])
    lines.extend(f"    from pyslang import {module}" for module in submodules)
    lines.extend(
        f"    reveal_type({module}.{member})"
        for module, member in submodule_probe_members.items()
    )

    path = tmp_path_factory.mktemp("stub-check") / "example.py"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def _checker_command(name: str) -> list[str]:
    """Use a type checker installed in the test interpreter when possible."""
    if importlib.util.find_spec(name) is not None:
        return [sys.executable, "-m", name]

    executable = shutil.which(name)
    if executable is None:
        pytest.skip(f"{name} is not installed")
    return [executable]


def _format_diagnostics(diagnostics: list[dict[str, object]]) -> str:
    """Format checker diagnostics for assertion failures."""
    return "\n".join(
        f"  {diagnostic.get('file', '<unknown>')}:{diagnostic.get('line', '?')}: "
        f"{diagnostic.get('message', '<no message>')}"
        for diagnostic in diagnostics
    )


@pytest.fixture(scope="session")
def checker_command():
    return _checker_command


@pytest.fixture(scope="session")
def format_diagnostics():
    return _format_diagnostics
