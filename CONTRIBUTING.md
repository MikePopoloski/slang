# Contributing to slang

## Getting started

Make sure to read the [Developer Guide](https://sv-lang.com/developer-guide.html) first.

Before submitting a PR, consider opening a discussion first about the change you want to make. There's nothing more frustrating for you as well as for the project maintainers for someone to submit a huge diff and ultimately it be rejected due to heading in the wrong direction for the project's goals.

New changes will almost always require corresponding unit tests and likely updates to documentation as well. Please be prepared to provide those, as the project aims to maintain a high standard for code quality and maintainability.

Otherwise, happy hacking and thanks for contributing!

## Builds and Warnings

CI builds are run with high warnings levels. It's highly recommended that you run locally with those same settings to avoid long iteration cycles of uploading changes and finding they break the CI build. You can use CMake's presets functionality with some of the presets included in the CMakePresets.json file. Customize them for your local system by creating a CMakeUserPresets.json file locally and inheriting your configurations from one of the project-level presets.

## Style and Coding Guidelines

The project's coding standards are loosely based on the [LLVM Coding Standards](https://llvm.org/docs/CodingStandards.html) with some exceptions. A non-exhaustive list is as follows:
* Column width is 100
* Functions, parameters, and local variables are lowerCase named instead of UpperCase named.
* Header ifdef guards are not used -- #pragma once is sufficient
* Exceptions are permitted, though not necessarily encouraged

In general the existing code is pretty consistent so please try to follow the patterns you see when making changes.

All proposed changes must be run through clang-format with the project's local settings as well as pass pre-commit checks. Most editors can be configured to run clang-format for you automatically. Additionally as a helpful hint, you can "install" pre-commit hooks into your local checkout and have them run automatically on every commit so that you don't forget:

    pip install pre-commit
    pre-commit install

All documentation should adhere to the [Google Developer Documentation Style
Guide](https://developers.google.com/style).

## Licensing

By submitting a pull request or a patch, you represent that you have the right to license your contribution to the slang project owners and the community, agree that your contributions are licensed under the slang license, and agree to future changes to the licensing.
