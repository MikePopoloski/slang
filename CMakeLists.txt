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

# Determine our project version by looking at git tags.
set(CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake" ${CMAKE_MODULE_PATH})
include(gitversion)
get_git_version(SLANG_VERSION_MAJOR SLANG_VERSION_MINOR SLANG_VERSION_PATCH
                SLANG_VERSION_HASH SLANG_VERSION_STRING)

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

option(SLANG_COVERAGE "Enable code coverage" OFF)
option(CI_BUILD "Enable longer running tests for CI builds" OFF)
option(FUZZ_TARGET "Enables changes to make binaries easier to fuzz test" OFF)
option(SLANG_INCLUDE_TOOLS "Include tools targets in the build"
       ${SLANG_MASTER_PROJECT})
option(SLANG_INCLUDE_TESTS "Include test targets in the build"
       ${SLANG_MASTER_PROJECT})
option(SLANG_INCLUDE_DOCS "Include documentation targets in the build" OFF)
option(SLANG_INCLUDE_LLVM "Include LLVM in the build for code generation" OFF)
option(SLANG_INCLUDE_PYLIB "Include the pyslang python module in the build" OFF)
option(SLANG_INCLUDE_INSTALL "Include installation targets"
       ${SLANG_MASTER_PROJECT})
option(STATIC_BUILD "Make the linked binaries static" OFF)
option(BUILD_SHARED_LIBS "Generate a shared library instead of static" OFF)
option(SLANG_RUN_CLANG_TIDY "Run clang-tidy during the build" OFF)
set(SLANG_WARN_FLAGS
    ""
    CACHE STRING "Extra warning flags to apply to the slang library build")
set(DOXYGENPY_PATH
    ""
    CACHE STRING "When building docs, the path to doxygen.py tool")

set(SLANG_SANITIZERS
    ""
    CACHE STRING "List of Clang sanitizers to include in build")

# Include built-in cmake modules.
include(GNUInstallDirs)
include(CMakePackageConfigHelpers)

# Variables used by subdirectories.
set(SCRIPTS_DIR ${PROJECT_SOURCE_DIR}/scripts)
if(NOT SLANG_EXPORT_NAME)
  set(SLANG_EXPORT_NAME "${PROJECT_NAME}Targets")
endif()

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
  add_compile_definitions(WIN32)
  add_compile_definitions(_WINDOWS)
  add_compile_definitions(NOMINMAX)
  add_compile_definitions(UNICODE)
  add_compile_definitions(_UNICODE)
  add_compile_definitions(WIN32_LEAN_AND_MEAN)
  add_compile_definitions(_SCL_SECURE_NO_WARNINGS)
  add_compile_definitions(_CRT_SECURE_NO_WARNINGS)
  add_compile_definitions(_CRT_SECURE_NO_DEPRECATE)
  add_compile_definitions(_CRT_NONSTDC_NO_WARNINGS)
endif()

if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
  add_compile_options(/utf-8)
endif()

if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
  if(CMAKE_BUILD_TYPE MATCHES "Debug")
    add_compile_options(/DDEBUG)
  endif()
else()
  # Always include debug info
  add_compile_options(-g)

  if(CMAKE_BUILD_TYPE MATCHES "Debug")
    add_compile_options(-DDEBUG)
  endif()

  if(SLANG_COVERAGE)
    if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
      add_compile_options(-fprofile-instr-generate -fcoverage-mapping)
      link_libraries(-fprofile-instr-generate -fcoverage-mapping)
    else()
      add_compile_options(
        --coverage -fno-omit-frame-pointer -fno-optimize-sibling-calls
        -fno-inline -fno-inline-small-functions -fno-default-inline)
      link_libraries(--coverage)
    endif()
  endif()

  if(SLANG_SANITIZERS)
    add_compile_options("-fsanitize=${SLANG_SANITIZERS}")
    link_libraries("-fsanitize=${SLANG_SANITIZERS}")
  endif()
endif()

if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-xc++)

  if(APPLE)
    set(CMAKE_SHARED_LIBRARY_CREATE_CXX_FLAGS
        "${CMAKE_SHARED_LIBRARY_CREATE_CXX_FLAGS} -undefined dynamic_lookup")
    if(STATIC_BUILD)
      message(SEND_ERROR "STATIC_BUILD=ON not supported on macOS.")
    endif()
  endif()
endif()

if(NOT SLANG_USE_SYSTEM_LIBS)
  if(SLANG_INCLUDE_INSTALL)
    set(FMT_INSTALL ON)
    set(FMT_CMAKE_DIR "${CMAKE_INSTALL_DATAROOTDIR}/cmake/fmt")
    set(FMT_PKGCONFIG_DIR "${CMAKE_INSTALL_DATAROOTDIR}/pkgconfig")
  endif()
  add_subdirectory(external/fmt)
endif()

add_subdirectory(source)

if(SLANG_INCLUDE_TOOLS)
  add_subdirectory(tools)
endif()

if(SLANG_INCLUDE_TESTS)
  include(CTest)
  add_subdirectory(external/Catch2)

  add_subdirectory(tests/regression)
  add_subdirectory(tests/unittests)

  if(SLANG_INCLUDE_LLVM)
    add_subdirectory(tests/simtests)
  endif()
endif()

if(SLANG_INCLUDE_DOCS)
  add_subdirectory(docs)
endif()

if(SLANG_INCLUDE_PYLIB)
  add_subdirectory(external/pybind11)
  add_subdirectory(bindings)
endif()

if(SLANG_INCLUDE_INSTALL)
  # Package export / installation rules
  set(SLANG_CMAKECONFIG_INSTALL_DIR
      "${CMAKE_INSTALL_DATAROOTDIR}/cmake/${PROJECT_NAME}"
      CACHE STRING "install path for slangConfig.cmake")

  install(
    EXPORT ${SLANG_EXPORT_NAME}
    NAMESPACE "slang::"
    DESTINATION ${SLANG_CMAKECONFIG_INSTALL_DIR})

  configure_package_config_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/cmake/slangConfig.cmake.in
    "${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}Config.cmake"
    INSTALL_DESTINATION ${SLANG_CMAKECONFIG_INSTALL_DIR})

  write_basic_package_version_file(
    ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}ConfigVersion.cmake
    VERSION ${PROJECT_VERSION}
    COMPATIBILITY SameMajorVersion)

  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}Config.cmake
                ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}ConfigVersion.cmake
          DESTINATION ${SLANG_CMAKECONFIG_INSTALL_DIR})

  if(UNIX)
    # Install pkg-config input file
    configure_file(${CMAKE_CURRENT_SOURCE_DIR}/scripts/sv-lang.pc.in
                   ${CMAKE_CURRENT_BINARY_DIR}/sv-lang.pc @ONLY)
    install(FILES ${CMAKE_CURRENT_BINARY_DIR}/sv-lang.pc
            DESTINATION ${CMAKE_INSTALL_DATAROOTDIR}/pkgconfig)
  endif()
endif()
