# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import sys as _sys

from pyslang.pyslang import *
from pyslang.pyslang import __version__ as __version__
from pyslang.pyslang import (
    analysis,
    ast,
    driver,
    parsing,
    syntax,
)

for _name, _mod in [
    ("pyslang.ast", ast),
    ("pyslang.syntax", syntax),
    ("pyslang.parsing", parsing),
    ("pyslang.analysis", analysis),
    ("pyslang.driver", driver),
]:
    _sys.modules[_name] = _mod
