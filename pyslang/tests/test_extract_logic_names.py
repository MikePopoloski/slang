# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

"""Tests for the logic declaration name extractor example."""

import pytest

from extract_logic_names import (
    LogicDeclarationExtractor,
    extract_logic_declaration_names,
    extract_logic_declarations_from_file,
)
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


def test_logic_declaration_extractor():
    """Test the LogicDeclarationExtractor class directly."""

    code = """
    module test_module;
        logic        clk;
        logic [7:0]  data;
        bit          bit_sig;
        reg [3:0]    reg_sig;
        logic        enable;
        int          counter;
        logic [1:0]  state;
    endmodule
    """

    tree = SyntaxTree.fromText(code)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)

    extractor = LogicDeclarationExtractor()
    compilation.getRoot().visit(extractor)

    assert set(extractor.logic_names) == {"clk", "data", "enable", "state"}


def test_extract_logic_declaration_names_function():
    code = """
    module simple_test;
        logic        reset;
        logic [15:0] address;
        bit          ready;
        logic        valid;
    endmodule
    """

    assert set(extract_logic_declaration_names(code)) == {"reset", "address", "valid"}


def test_no_logic_declarations():
    code = """
    module no_logic;
        bit        a;
        reg [7:0]  b;
        int        c;
        wire       d;
    endmodule
    """

    assert extract_logic_declaration_names(code) == []


def test_complex_module_with_ports():
    code = """
    module complex_test(
        input  logic        clk,
        input  logic        reset_n,
        input  logic [7:0]  data_in,
        output logic [15:0] data_out,
        output logic        valid
    );
        logic [3:0]  internal_counter;
        logic        internal_enable;
        bit          bit_flag;
        reg [1:0]    reg_state;
        logic        ready;
    endmodule
    """

    assert set(extract_logic_declaration_names(code)) == {
        "clk",
        "reset_n",
        "data_in",
        "data_out",
        "valid",
        "internal_counter",
        "internal_enable",
        "ready",
    }


def test_logic_arrays_and_vectors():
    code = """
    module array_test;
        logic           single_bit;
        logic [7:0]     byte_vector;
        logic [15:0]    word_vector;
        logic [31:0]    dword_vector;
        logic [1:0][7:0] multi_dim;
    endmodule
    """

    assert set(extract_logic_declaration_names(code)) == {
        "single_bit",
        "byte_vector",
        "word_vector",
        "dword_vector",
        "multi_dim",
    }


def test_extract_from_file(tmp_path):
    sv_file = tmp_path / "module.sv"
    sv_file.write_text("module m; logic foo; bit b; endmodule")
    assert extract_logic_declarations_from_file(str(sv_file)) == ["foo"]


def test_extract_from_missing_file(tmp_path):
    with pytest.raises(FileNotFoundError):
        extract_logic_declarations_from_file(str(tmp_path / "missing.sv"))
