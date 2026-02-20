# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import sys as _sys

from pyslang.pyslang import *  # noqa: F401,F403
from pyslang.pyslang import driver  # noqa: F401
from pyslang.pyslang import __version__, analysis, ast, parsing, syntax

for _name, _mod in [
    ("pyslang.ast", ast),
    ("pyslang.syntax", syntax),
    ("pyslang.parsing", parsing),
    ("pyslang.analysis", analysis),
    ("pyslang.driver", driver),
]:
    _sys.modules[_name] = _mod
