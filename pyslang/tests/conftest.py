# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import gc
import sys
from pathlib import Path
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "examples"))

@pytest.fixture(autouse=True)
def _auto_gc():
    # This avoids false-postive leak warnings caused by test-harness variable
    # caching.
    yield
    gc.collect()
