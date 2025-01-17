# Contributing to `pyslang`

Pyslang, the Python bindings for the [slang project](https://github.com/MikePopoloski/slang), are built, tested, and packaged with code in this repository.

The bulk of functional code is in the [`slang` repository](https://github.com/MikePopoloski/slang). Please refer to its [CONTRIBUTING.md](https://github.com/MikePopoloski/slang/blob/master/CONTRIBUTING.md) guide for more information on contributing to the core project.

## Python Bindings

Python bindings are built using [pybind11](https://github.com/pybind/pybind11).

## Documentation

All documentation is contained in the `docs` directory of the `slang` repository.

## Building and Testing

1. Clone the `pyslang` repository (https://github.com/MikePopoloski/pyslang)
2. Clone the `slang` submodule:

```bash
git submodule update --init --recursive
```

3. Optionally, create a virtual environment and activate it.

```bash
python3 -m venv venv
source venv/bin/activate
```

4. Install `pyslang` as a Python package (including building the C++ `slang` library with bindings, from the submodule):

```bash
pip install .
```
