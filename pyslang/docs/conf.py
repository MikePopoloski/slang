# Docs: https://mcss.mosra.cz/documentation/python/
# Run this file with `<mcss_clone_path>/documentation/python.py <path_to_this_file>`

import os

root_dir = os.environ["DOC_OUTPUT_DIR"]

# Set the m.css configuration variables.
PROJECT_TITLE = "pyslang"
INPUT_MODULES = ["pyslang"]
PYBIND11_COMPATIBILITY = True
OUTPUT = root_dir

INPUT_PAGES = [
    "pages/index.rst",  # Custom home page. `index.rst` gets used as the homepage by default.
]

LINKS_NAVBAR1 = [
    ("Slang Documentation", "/", []),
    ("GitHub", "https://github.com/MikePopoloski/slang", []),
    ("PyPI", "https://pypi.org/project/pyslang/", []),
    # Default links:
    ("Pages", "pages", []),
    ("Modules", "modules", []),
    ("Classes", "classes", []),
]

# Output the stubs for comparison/review, but not actually used.
OUTPUT_STUBS = os.path.join(OUTPUT, "stubs")
