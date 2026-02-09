import sys

from pyslang.pyslang import ast, syntax, parsing, analysis, driver, numeric, diagnostics, text  # noqa: F401
from pyslang.pyslang import BumpAllocator, Bag, VersionInfo  # noqa: F401

for _name, _mod in [
    ("pyslang.ast", ast),
    ("pyslang.syntax", syntax),
    ("pyslang.parsing", parsing),
    ("pyslang.analysis", analysis),
    ("pyslang.driver", driver),
    ("pyslang.numeric", numeric),
    ("pyslang.diagnostics", diagnostics),
    ("pyslang.text", text),
]:
    sys.modules[_name] = _mod
