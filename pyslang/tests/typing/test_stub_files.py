# SPDX-FileCopyrightText: Benjamin Davis
# SPDX-License-Identifier: MIT

import ast
from pathlib import Path

import pytest

import pyslang


@pytest.mark.parametrize(
    "stub_directory",
    [
        pytest.param(
            Path(pyslang.__file__).resolve().parent,
            id="public-package",
        ),
        pytest.param(
            Path(pyslang.__file__).resolve().parent / "pyslang",
            id="extension-package",
        ),
    ],
)
def test_submodule_stub_files_exist(stub_directory: Path, submodules: tuple[str, ...]):
    """Each exposed sub-module should ship a companion ``.pyi`` stub file."""
    present = sorted(path.name for path in stub_directory.glob("*.pyi"))
    missing = [
        module
        for module in submodules
        if not (stub_directory / f"{module}.pyi").exists()
    ]
    assert not missing, (
        f"No type stub (.pyi) files for sub-modules {missing}.\n"
        f"Stub files actually shipped in {stub_directory}: {present}"
    )


# Both install locations ship the generated stubs: the package root (where
# __init__.py re-exports the sub-modules into sys.modules) and the compiled
# extension's own package directory.
_PACKAGE_ROOT = Path(pyslang.__file__).resolve().parent

_STUB_FILES = [
    pytest.param(path, id=f"{label}-{path.stem}")
    for label, directory in (
        ("public-package", _PACKAGE_ROOT),
        ("extension-package", _PACKAGE_ROOT / "pyslang"),
    )
    for path in sorted(directory.glob("*.pyi"))
]


@pytest.mark.parametrize("stub_file", _STUB_FILES)
def test_stub_file_is_valid_python(stub_file: Path) -> None:
    """Every shipped stub file must parse as valid Python.

    The stubs are generated from C++ bindings whose names come from the
    SystemVerilog grammar, so binding mistakes can produce stubs that cannot
    be parsed at all: Python keywords used as argument names (``with``),
    non-identifier enum member names (``$bits``, ``None``), or defaulted
    arguments followed by required ones. Type checkers report such files only
    as a bare "Invalid syntax" for the whole file, so each stub is parsed
    here to pinpoint the exact file and line instead.
    """
    source = stub_file.read_text(encoding="utf-8")
    try:
        ast.parse(source, filename=str(stub_file))
    except SyntaxError as error:
        line = (error.text or "<source line unavailable>").strip()
        if len(line) > 120:
            line = line[:117] + "..."
        pytest.fail(
            "Stub file does not parse as valid Python:\n"
            f"  {stub_file}:{error.lineno}: {error.msg}\n"
            f"  {line}\n"
            "\n"
            "Stub files are generated from the bindings; fix the binding that "
            "produces this declaration (not the .pyi file itself) and rebuild "
            "to regenerate the stubs."
        )
