from setuptools import find_packages
from skbuild import setup

setup(
    version="2.0.0",
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
