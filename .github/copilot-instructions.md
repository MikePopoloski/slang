This project is a SystemVerilog compiler and set of related tools, developed in C++.
Code in the repository is expected to be extremely high quality, with a focus on performance and correctness.
Please follow the instructions below to ensure that your contributions meet these standards.

## Development Flow
cmake is used to build the project. The following commands are used to build and run the tests:
```bash
cmake -B build
cmake --build build -j8
ctest --test-dir build --output-on-failure
```

## Code Style
Please follow the style of the existing code. Modern C++ features, up to C++ 20, are preferred, and the code should
be written in a way that is easy to read and understand.

`pre-commit` is used to enforce formatting prior to committing. It should be installed and configured to run
automatically on commit.

## Guidelines
1. Follow C++ best practices and idiomatic patterns
2. Maintain existing code structure and organization
3. Write unit tests for new functionality.
4. Document public APIs and complex logic.
    - API reference documentation is added via Doxygen comments.
    - More in-depth documentation is added via Markdown files in the `docs` directory.

## Python Bindings
This project includes Python bindings fsor the main library. These bindings are generated using pybind11.
When adding to or changing the public API, consider updating the Python bindings as well.
The bindings are located in the `bindings/python` directory. The tests and documentation for the Python bindings
are in the 'pyslang' folder. The bindings are built using CMake, and the following commands
are used to build and run the tests:
```bash
pip install . --no-build-isolation --config-settings build-dir=build/python_build
pytest
```
