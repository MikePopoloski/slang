from subprocess import check_output

from setuptools import find_packages
from skbuild import setup

command = "git describe --tags --long --dirty"
fmt = "{tag}+{commitcount}.{gitsha}"

git_version = check_output(command.split()).decode("utf-8").strip()
if git_version.startswith("v"):
    git_version = git_version[1:]

parts = git_version.split("-")
assert len(parts) in (3, 4)
dirty = len(parts) == 4
tag, count, sha = parts[:3]
if count == "0" and not dirty:
    version = tag
else:
    version = fmt.format(tag=tag, commitcount=count, gitsha=sha)
    if dirty:
        version = version + ".dirty"

setup(
    version=version,
    packages=[""],
    package_dir={"": "source"},
    cmake_source_dir="../",
    cmake_install_dir="source",
    cmake_install_target="pyslang-install-pylib",
    cmake_args=[
        "-DSLANG_INCLUDE_TESTS=OFF",
        "-DSLANG_INCLUDE_TOOLS=OFF",
        "-DSLANG_INCLUDE_PYLIB=ON",
    ],
    include_package_data=True,
    extras_require={"test": ["pytest"]},
)
