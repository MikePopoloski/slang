from setuptools import find_packages
from skbuild import setup

setup(
    name="pyslang",
    version="2.0.0",
    description="Python bindings for slang, a library for compiling SystemVerilog",
    author="Mike Popoloski",
    license="MIT",
    packages=find_packages(where="source"),
    package_dir={"": "source"},
    cmake_source_dir="../",
    cmake_install_dir="source/pyslang",
    cmake_install_target="pyslang-install-pylib",
    cmake_args=[
        "-DSLANG_INCLUDE_TESTS=OFF",
        "-DSLANG_INCLUDE_TOOLS=OFF",
        "-DSLANG_INCLUDE_PYLIB=ON",
    ],
    include_package_data=True,
    extras_require={"test": ["pytest"]},
    python_requires=">=3.6",
)
