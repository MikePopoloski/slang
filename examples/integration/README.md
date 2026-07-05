# slang integration example

This directory is a small example of consuming the
[slang](https://github.com/MikePopoloski/slang) library from your own CMake
build. The same `main.cpp` (a minimal driver front-end) is built against slang
using either of the two supported integration methods, selected at configure
time with `-DSLANG_EXAMPLE_METHOD`:

| Method | `SLANG_EXAMPLE_METHOD` | How slang is obtained |
| ------ | ---------------------- | --------------------- |
| External package | `package` | `find_package(slang)` locates a pre-installed copy |
| Subproject | `subproject` (default) | `FetchContent` builds slang from source as part of this build |

In all cases the project simply links against the `slang::slang` CMake target;
everything else is set up automatically.

See the [Integration](https://sv-lang.com/building.html#integration) section of
the slang documentation for more details.

## Building as a subproject (default)

No separate installation step is required; the first configure downloads the
slang source from GitHub, so it may take a little while:

```
cmake -B build -DSLANG_EXAMPLE_METHOD=subproject
cmake --build build -j
```

slang can also equivalently be used via a git submodule and an
`add_subdirectory` call.

## Building against an installed package

First build and install slang somewhere (here we install into a local `prefix`
directory):

```
cmake -B build/slang -S <path-to-slang> -DCMAKE_INSTALL_PREFIX=$PWD/prefix
cmake --build build/slang -j
cmake --install build/slang --component slang_Development --strip
```

Then configure and build this example, pointing CMake at the install prefix so
`find_package` can locate slang:

```
cmake -B build -DSLANG_EXAMPLE_METHOD=package -DCMAKE_PREFIX_PATH=$PWD/prefix
cmake --build build -j
```
