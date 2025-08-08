# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Build the project
cmake -B build/macos-claude
cmake --build build/macos-claude -j8

# Run tests
ctest --test-dir build/macos-claude --output-on-failure

# Python bindings build and test
pip install . --no-build-isolation --config-settings build-dir=build/claude_python_build
pytest
```

## Testing Framework

- **Unit Tests**: Uses Catch2 framework, located in `tests/unittests/`
- **Regression Tests**: Custom SystemVerilog test files in `tests/regression/`
- **Test Command**: `ctest --test-dir build/macos-claude --output-on-failure`
- **Python Tests**: `pytest` (for Python bindings)

## Architecture Overview

The slang library is organized into several key subsystems:

1. **Text Processing** (`source/text/`): Source management, location tracking, globbing
2. **Lexing & Parsing** (`source/parsing/`): Tokenization, preprocessor, parser
3. **Syntax Tree** (`source/syntax/`): AST representation and manipulation
4. **Semantic Analysis** (`source/ast/`): Type checking, symbol resolution, compilation
5. **Diagnostics** (`source/diagnostics/`): Error reporting and formatting
6. **Numeric** (`source/numeric/`): SystemVerilog numeric types and operations
7. **Analysis** (`source/analysis/`): Data flow analysis, assertion analysis, driver tracking
8. **Utilities** (`source/util/`): Memory management, containers, OS abstractions

### Tools Included

- **slang**: Main compiler driver (`tools/driver/`)
- **slang-tidy**: Linting and style checking tool (`tools/tidy/`)
- **slang-reflect**: Type reflection utility (`tools/reflect/`)
- **slang-rewriter**: Code transformation tool (`tools/rewriter/`)
- **slang-hier**: Hierarchy analysis tool (`tools/hier/`)

## Code Style and Standards

- Follow existing C++ code style (enforced by pre-commit hooks)
- Use modern C++20 features and idioms
- Write unit tests for new functionality
- Document public APIs with Doxygen comments
- Maintain high performance and correctness standards
- Python bindings should be updated when changing public APIs

## Development Workflow

1. Build: `cmake -B build/macos-claude && cmake --build build/macos-claude -j8`
2. Test: `ctest --test-dir build/macos-claude --output-on-failure`
3. Format: Automatic via pre-commit hooks
4. For Python changes: `pip install . --no-build-isolation --config-settings build-dir=build/claude_python_build && pytest`

## Project Structure

This is a SystemVerilog compiler and language services library that provides:
- Complete SystemVerilog parsing, analysis, and elaboration
- High-performance compilation with excellent error messages
- Python bindings for integration into other tools
- Various command-line tools for SystemVerilog development
