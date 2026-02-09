import sys

from pyslang.pyslang import (Bag, BumpAllocator, VersionInfo,  # noqa: F401
                             __version__, analysis, ast, diagnostics, driver,
                             numeric, parsing, syntax, text)

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
