# Docs: https://mcss.mosra.cz/documentation/python/
# Run this file with `<mcss_clone_path>/documentation/python.py <path_to_this_file>`

from pathlib import Path

# Find the root of the git repository.
_GIT_REPO_ROOT_PATH = Path(__file__).parent.parent.parent
assert (_GIT_REPO_ROOT_PATH / ".git").is_dir(), "Git repository root not found/set incorrectly"

# Set the m.css configuration variables.
PROJECT_TITLE = "pyslang"
INPUT_MODULES = ["pyslang"]
PYBIND11_COMPATIBILITY = True
OUTPUT = str((_GIT_REPO_ROOT_PATH / "build/docs").absolute())

# Output the stubs for comparison/review, but not actually used.
OUTPUT_STUBS = str((_GIT_REPO_ROOT_PATH / "build/stubs").absolute())
