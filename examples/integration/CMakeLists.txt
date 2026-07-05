# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

cmake_minimum_required(VERSION 3.28)

project(slang_example CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# This example demonstrates the two supported ways of consuming slang from an
# external CMake build (see docs/building.dox, "Integration"):
#
# package    - locate a pre-installed slang via find_package() subproject -
# build slang from source as part of this build via FetchContent
#
# Pick one by configuring with -DSLANG_EXAMPLE_METHOD=package|subproject.
#
# When this example is built as part of the slang tree itself (via
# SLANG_INCLUDE_EXAMPLES) the slang::slang target already exists, so neither
# acquisition method is needed and we simply reuse it. This lets slang's own CI
# verify that the example source still compiles against the current API.
if(NOT TARGET slang::slang)
  set(SLANG_EXAMPLE_METHOD
      "subproject"
      CACHE
        STRING
        "How to consume slang: 'package' (find_package) or 'subproject' (FetchContent)"
  )
  set_property(CACHE SLANG_EXAMPLE_METHOD PROPERTY STRINGS package subproject)

  if(SLANG_EXAMPLE_METHOD STREQUAL "package")
    find_package(slang 11.0.0 REQUIRED)
  elseif(SLANG_EXAMPLE_METHOD STREQUAL "subproject")
    # Note: this example just pulls the head master branch for slang, but a real
    # project would very likely pin this to a specific tag and only update when
    # ready to accept a new version.
    include(FetchContent)
    FetchContent_Declare(
      slang
      GIT_REPOSITORY https://github.com/MikePopoloski/slang.git
      GIT_SHALLOW ON)
    FetchContent_MakeAvailable(slang)
  else()
    message(
      FATAL_ERROR
        "Unknown SLANG_EXAMPLE_METHOD '${SLANG_EXAMPLE_METHOD}'; expected 'package' or 'subproject'"
    )
  endif()
endif()

add_executable(slang_example main.cpp)
target_link_libraries(slang_example PRIVATE slang::slang)
