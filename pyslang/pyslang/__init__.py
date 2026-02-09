import sys as _sys

from pyslang.pyslang import *  # noqa: F401,F403
from pyslang.pyslang import __version__, ast, syntax, parsing, analysis, driver  # noqa: F401

for _name, _mod in [
    ("pyslang.ast", ast),
    ("pyslang.syntax", syntax),
    ("pyslang.parsing", parsing),
    ("pyslang.analysis", analysis),
    ("pyslang.driver", driver),
]:
    _sys.modules[_name] = _mod
