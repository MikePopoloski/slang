# Docs: https://mcss.mosra.cz/documentation/doxygen/#configuration

import os

# File is generated from CMake, from "Doxyfile.in"
DOXYFILE = os.environ["DOXYFILE_PATH"]

LINKS_NAVBAR1 = [
    (
        "User Manual",
        "user-manual",
        [
            ("Command Line Reference", "command-line-ref"),
            ("Language Support", "language-support"),
            ("Warning Reference", "warning-ref"),
            ("Tools", "tools"),
        ],
    ),
    (
        "Developer Guide",
        "developer-guide",
        [
            ("Building", "building"),
            ("Common Components", "commoncomp"),
            ("Source Management", "sourcemanagement"),
            ("Diagnostics", "diagnostics"),
            ("Parsing", "parsing"),
        ],
    ),
]

LINKS_NAVBAR2 = [
    (
        "API Reference",
        "api-reference",
        [
            ("Namespaces", "namespaces"),
            ("Classes", "annotated"),
        ],
    ),
    ("Try It", "https://sv-lang.com/explore/", []),
    ("GitHub", "https://github.com/MikePopoloski/slang", []),
]

FINE_PRINT = (
    "<p>slang SystemVerilog language services. Copyright (C) 2015-2025 Michael Popoloski.</br>"
    'Code is <a href="https://github.com/MikePopoloski/slang">available on GitHub</a> under the MIT license.</p>'
)
SEARCH_DOWNLOAD_BINARY = True
SEARCH_BASE_URL = "https://sv-lang.com/"
SEARCH_EXTERNAL_URL = "https://google.com/search?q=site:sv-lang.com+{query}"
