# SPDX-FileCopyrightText: Benjamin Davis
# SPDX-License-Identifier: MIT

import pytest

import pyslang


@pytest.mark.parametrize("flag_class", [pyslang.ast.ASTFlags])
def test_flags_none_members_exist(flag_class):
    assert hasattr(flag_class, "None_")
