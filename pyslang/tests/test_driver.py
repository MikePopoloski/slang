# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pathlib import Path

from pyslang import BufferID
from pyslang.driver import CommandLineOptions, Driver


def _write_driver_sources(tmp_path):
    header = tmp_path / "included.svh"
    top = tmp_path / "top.sv"

    header.write_text(
        """`ifndef INCLUDED_SVH
`define INCLUDED_SVH
logic included_signal;
`endif
"""
    )
    top.write_text(
        """module m;
`include "included.svh"
`include "included.svh"
endmodule
"""
    )

    return top


def _create_driver(top):
    driver = Driver()
    driver.addStandardArgs()

    # Use a quoted POSIX-style path so backslashes in Windows paths aren't
    # treated as escape characters by the command-line tokenizer.
    assert driver.parseCommandLine(
        f'slang "{Path(top).as_posix()}"', CommandLineOptions()
    )
    assert driver.processOptions()

    return driver


def test_parse_all_sources_buffer_change_cb(tmp_path):
    top = _write_driver_sources(tmp_path)
    driver = _create_driver(top)

    events = []

    def buffer_change_cb(buffer, is_back, is_skip):
        events.append((buffer, is_back, is_skip))

    assert driver.parseAllSources(buffer_change_cb)
    assert len(driver.syntaxTrees) == 1

    normalized_events = []
    for buffer, is_back, is_skip in events:
        assert isinstance(buffer, BufferID)
        assert isinstance(is_back, bool)
        assert isinstance(is_skip, bool)

        normalized_events.append(
            (
                Path(driver.sourceManager.getFullPath(buffer)).name,
                driver.sourceManager.getBufferKind(buffer).name,
                is_back,
                is_skip,
            )
        )

    assert normalized_events == [
        ("top.sv", "DesignFile", False, False),
        ("included.svh", "IncludeFile", False, False),
        ("top.sv", "DesignFile", True, False),
        ("included.svh", "IncludeFile", False, True),
    ]


def test_parse_all_sources_without_buffer_change_cb(tmp_path):
    top = _write_driver_sources(tmp_path)
    driver = _create_driver(top)

    assert driver.parseAllSources()
    assert len(driver.syntaxTrees) == 1
    assert list(driver.sourceLoader.errors) == []
