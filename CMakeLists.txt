# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# slang - cmake entry point
cmake_minimum_required(VERSION 3.15...3.24)

# Determine if slang is built as a subproject (using add_subdirectory) or if it
# is the master project.
if(NOT DEFINED SLANG_MASTER_PROJECT)
  set(SLANG_MASTER_PROJECT OFF)
  if(CMAKE_CURRENT_SOURCE_DIR STREQUAL CMAKE_SOURCE_DIR)
    set(SLANG_MASTER_PROJECT ON)
    message(STATUS "CMake version: ${CMAKE_VERSION}")
  endif()
endif()

# Protect against in-tree builds.
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR)
  message(
    FATAL_ERROR "In-source builds are not supported. You may need to delete "
                "'CMakeCache.txt' and 'CMakeFiles/' before building again.")
endif()

# Determine our patch version by looking at git tags.
set(CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake" ${CMAKE_MODULE_PATH})
include(gitversion)
get_git_version(SLANG_VERSION_PATCH SLANG_VERSION_HASH)

set(SLANG_VERSION_MAJOR 3)
set(SLANG_VERSION_MINOR 0)
set(SLANG_VERSION_STRING
    "${SLANG_VERSION_MAJOR}.${SLANG_VERSION_MINOR}.${SLANG_VERSION_PATCH}")
message(STATUS "slang version: ${SLANG_VERSION_STRING}+${SLANG_VERSION_HASH}")

# Set the default build type if none is set explicitly, but only for
# single-config generators.
get_property(isMultiConfig GLOBAL PROPERTY GENERATOR_IS_MULTI_CONFIG)
if(SLANG_MASTER_PROJECT
   AND NOT isMultiConfig
   AND NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE
      Release
      CACHE
        STRING
        "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel."
        FORCE)
endif()

project(
  slang
  VERSION ${SLANG_VERSION_STRING}
  LANGUAGES CXX
  HOMEPAGE_URL https://sv-lang.com/
  DESCRIPTION "SystemVerilog compiler and language services")

option(SLANG_INCLUDE_TOOLS "Include tools targets in the build"
       ${SLANG_MASTER_PROJECT})
option(SLANG_INCLUDE_TESTS "Include test targets in the build"
       ${SLANG_MASTER_PROJECT})
option(SLANG_INCLUDE_DOCS "Include documentation targets in the build" OFF)
option(SLANG_INCLUDE_PYLIB "Include the pyslang python module in the build" OFF)
option(SLANG_INCLUDE_INSTALL "Include installation targets"
       ${SLANG_MASTER_PROJECT})
option(SLANG_INCLUDE_COVERAGE "Enable code coverage" OFF)
option(SLANG_CI_BUILD "Enable longer running tests for CI builds" OFF)
option(SLANG_FUZZ_TARGET "Enables changes to make binaries easier to fuzz test"
       OFF)
option(BUILD_SHARED_LIBS "Generate shared libraries instead of static" OFF)

set(SLANG_LIB_NAME
    "svlang"
    CACHE STRING "Default output library name")

set(SLANG_CLANG_TIDY
    ""
    CACHE STRING "Run clang-tidy during the build with the given binary")
set(SLANG_WARN_FLAGS
    ""
    CACHE STRING "Extra warning flags to apply to the slang library build")

# Variables used by subdirectories.
include(FetchContent)
include(GNUInstallDirs)
set(SCRIPTS_DIR ${PROJECT_SOURCE_DIR}/scripts)

# Find Python. If we're building python bindings we need the development modules
# as well.
if(SLANG_INCLUDE_PYLIB)
  find_package(Python REQUIRED COMPONENTS Interpreter Development.Module)
else()
  find_package(Python REQUIRED COMPONENTS Interpreter)
endif()

# Set saner / consistent build directories on all platforms
foreach(
  var
  CMAKE_RUNTIME_OUTPUT_DIRECTORY
  CMAKE_RUNTIME_OUTPUT_DIRECTORY_RELEASE
  CMAKE_RUNTIME_OUTPUT_DIRECTORY_RELWITHDEBINFO
  CMAKE_RUNTIME_OUTPUT_DIRECTORY_MINSIZEREL
  CMAKE_RUNTIME_OUTPUT_DIRECTORY_DEBUG)
  if(NOT ${var})
    set(${var} ${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_INSTALL_BINDIR})
  endif()
endforeach()
foreach(
  var
  CMAKE_ARCHIVE_OUTPUT_DIRECTORY
  CMAKE_ARCHIVE_OUTPUT_DIRECTORY_RELEASE
  CMAKE_ARCHIVE_OUTPUT_DIRECTORY_RELWITHDEBINFO
  CMAKE_ARCHIVE_OUTPUT_DIRECTORY_MINSIZEREL
  CMAKE_ARCHIVE_OUTPUT_DIRECTORY_DEBUG
  CMAKE_LIBRARY_OUTPUT_DIRECTORY
  CMAKE_LIBRARY_OUTPUT_DIRECTORY_RELEASE
  CMAKE_LIBRARY_OUTPUT_DIRECTORY_RELWITHDEBINFO
  CMAKE_LIBRARY_OUTPUT_DIRECTORY_MINSIZEREL
  CMAKE_LIBRARY_OUTPUT_DIRECTORY_DEBUG)
  if(NOT ${var})
    set(${var} ${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_INSTALL_LIBDIR})
  endif()
endforeach()

# Always require C++17 or later, no extensions.
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Defaults for a bunch of Windows-specific junk. These are required by all
# targets to build and run correctly and don't affect ABI so shouldn't need
# target_ specific commands.
if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  add_compile_definitions(WIN32 _WINDOWS NTDDI_VERSION=0x06010000
                          _WIN32_WINNT=0x0601)
  add_compile_definitions(UNICODE _UNICODE NOMINMAX WIN32_LEAN_AND_MEAN)
  add_compile_definitions(_SCL_SECURE_NO_WARNINGS _CRT_SECURE_NO_WARNINGS)
  add_compile_definitions(_CRT_SECURE_NO_DEPRECATE _CRT_NONSTDC_NO_WARNINGS)

  # Project won't build out of the box without this flag.
  add_compile_options(/permissive-)
endif()

if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
  add_compile_options(/utf-8 /bigobj)
endif()

# Get sane install RPATH handling by default if none has been provided.
if(NOT CMAKE_INSTALL_RPATH AND BUILD_SHARED_LIBS)
  if(APPLE)
    set(base @loader_path)
  else()
    set(base $ORIGIN)
  endif()

  file(RELATIVE_PATH relDir ${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_INSTALL_BINDIR}
       ${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_INSTALL_LIBDIR})
  set(CMAKE_INSTALL_RPATH ${base} ${base}/${relDir})
endif()

set(STD_FS_LIB "")
# ==== The test below is based on:
# https://github.com/pybind/pybind11/blob/master/tests/CMakeLists.txt
#
# It is under a BSD-style license, see:
# https://github.com/pybind/pybind11/blob/master/LICENSE
#
# Check if we need to add -lstdc++fs or -lc++fs or nothing
if(DEFINED CMAKE_CXX_STANDARD AND CMAKE_CXX_STANDARD LESS 17)
  set(STD_FS_NO_LIB_NEEDED TRUE)
elseif(MSVC)
  set(STD_FS_NO_LIB_NEEDED TRUE)
else()
  file(
    WRITE ${CMAKE_CURRENT_BINARY_DIR}/main.cpp
    "#include <filesystem>\nint main(int argc, char ** argv) {\n  std::filesystem::path p(argv[0]);\n  return p.string().length();\n}"
  )
  try_compile(
    STD_FS_NO_LIB_NEEDED ${CMAKE_CURRENT_BINARY_DIR}
    SOURCES ${CMAKE_CURRENT_BINARY_DIR}/main.cpp
    COMPILE_DEFINITIONS -std=c++17)
  try_compile(
    STD_FS_NEEDS_STDCXXFS ${CMAKE_CURRENT_BINARY_DIR}
    SOURCES ${CMAKE_CURRENT_BINARY_DIR}/main.cpp
    COMPILE_DEFINITIONS -std=c++17
    LINK_LIBRARIES stdc++fs)
  try_compile(
    STD_FS_NEEDS_CXXFS ${CMAKE_CURRENT_BINARY_DIR}
    SOURCES ${CMAKE_CURRENT_BINARY_DIR}/main.cpp
    COMPILE_DEFINITIONS -std=c++17
    LINK_LIBRARIES c++fs)
endif()

if(NOT STD_FS_NO_LIB_NEEDED)
  if(STD_FS_NEEDS_STDCXXFS)
    set(STD_FS_LIB stdc++fs)
  elseif(STD_FS_NEEDS_CXXFS)
    set(STD_FS_LIB c++fs)
  endif()
endif()
# ==== (end of test for stdc++fs)

if(NOT "${STD_FS_LIB}" STREQUAL "")
  message(STATUS "Linking with: ${STD_FS_LIB}")
  list(APPEND SLANG_LIBRARIES ${STD_FS_LIB})
endif()

if(BUILD_SHARED_LIBS)
  message(STATUS "Build SHARED library as: ${SLANG_LIB_NAME}")
else()
  message(STATUS "Build STATIC library as: ${SLANG_LIB_NAME}")
endif()

include(external/CMakeLists.txt)
add_subdirectory(source)

if(SLANG_INCLUDE_TOOLS)
  add_subdirectory(tools)
endif()

if(SLANG_INCLUDE_TESTS)
  include(CTest)
  add_subdirectory(tests)
endif()

if(SLANG_INCLUDE_DOCS)
  add_subdirectory(docs)
endif()

if(SLANG_INCLUDE_PYLIB)
  add_subdirectory(bindings)
endif()

if(SLANG_INCLUDE_COVERAGE)
  include(cmake/coverage.cmake)
endif()

if(SLANG_INCLUDE_INSTALL)
  include(cmake/install-rules.cmake)
endif()

set(gitignore ${PROJECT_SOURCE_DIR}/.gitignore)
if(SLANG_MASTER_PROJECT AND EXISTS ${gitignore})
  # Get the list of ignored files from .gitignore.
  file(STRINGS ${gitignore} lines)
  list(REMOVE_ITEM lines /doc/html)
  foreach(line ${lines})
    string(REPLACE "/" "" line "${line}")
    string(REPLACE "." "[.]" line "${line}")
    string(REPLACE "*" ".*" line "${line}")
    set(ignored_files ${ignored_files} "${line}$" "${line}/")
  endforeach()
  set(ignored_files ${ignored_files} /.git)

  set(CPACK_PACKAGE_NAME slang)
  set(CPACK_PACKAGE_INSTALL_DIRECTORY slang)
  set(CPACK_PACKAGE_VENDOR "Michael Popoloski")
  set(CPACK_SOURCE_GENERATOR ZIP)
  set(CPACK_VERBATIM_VARIABLES YES)
  set(CPACK_SOURCE_IGNORE_FILES ${ignored_files})
  set(CPACK_SOURCE_PACKAGE_FILE_NAME slang-${SLANG_VERSION_STRING})
  set(CPACK_RESOURCE_FILE_README ${PROJECT_SOURCE_DIR}/README.md)
  include(CPack)
endif()
