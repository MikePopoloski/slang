import sys as _sys

from pyslang.pyslang import *  # noqa: F401,F403
from pyslang.pyslang import ast as ast
from pyslang.pyslang import syntax as syntax
from pyslang.pyslang import parsing as parsing
from pyslang.pyslang import analysis as analysis
from pyslang.pyslang import driver as driver
from pyslang.pyslang import __version__ as __version__

for _name, _mod in [
    ("pyslang.ast", ast),
    ("pyslang.syntax", syntax),
    ("pyslang.parsing", parsing),
    ("pyslang.analysis", analysis),
    ("pyslang.driver", driver),
]:
    _sys.modules[_name] = _mod
