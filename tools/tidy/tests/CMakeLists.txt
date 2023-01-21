# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~
set(find_pkg_args "")
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
  set(find_pkg_args "FIND_PACKAGE_ARGS" "3.0.0")
endif()

FetchContent_Declare(
  Catch2
  GIT_REPOSITORY https://github.com/catchorg/Catch2.git
  GIT_TAG v3.2.1
  GIT_SHALLOW ON
  ${find_pkg_args})
FetchContent_MakeAvailable(Catch2)

if(Catch2_FOUND)
  get_target_property(Catch2_INCLUDE_DIR Catch2::Catch2
                      INTERFACE_INCLUDE_DIRECTORIES)
  message(STATUS "Found system Catch2 version: ${Catch2_VERSION}")
  message(STATUS "Using system Catch2 include: ${Catch2_INCLUDE_DIR}")
else()
  message(STATUS "Using remote Catch2 library")
endif()

add_executable(
  tidy_unittests
  ../../../tests/unittests/main.cpp ../../../tests/unittests/Test.cpp
  ../synthesis/OnlyAssignedOnReset.cpp OnlyAssignedOnResetTest.cpp
  ../synthesis/RegisterHasNoReset.cpp RegisterHasNoResetTest.cpp)

target_link_libraries(
  tidy_unittests
  PRIVATE slang::slang Catch2::Catch2 fmt::fmt
  PUBLIC ${SLANG_LIBRARIES})
target_compile_definitions(tidy_unittests PRIVATE UNITTESTS)
target_include_directories(tidy_unittests PRIVATE ../include ../../../include
                                                  ../../../tests/unittests)

add_test(NAME tidy_unittests COMMAND tidy_unittests)
