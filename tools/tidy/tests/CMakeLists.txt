# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(
  tidy_unittests
  ../../../tests/unittests/main.cpp ../../../tests/unittests/Test.cpp
  ../synthesis/OnlyAssignedOnReset.cpp OnlyAssignedOnResetTest.cpp
  ../synthesis/RegisterHasNoReset.cpp RegisterHasNoResetTest.cpp)

target_link_libraries(tidy_unittests PRIVATE slang::slang Catch2::Catch2
                                             fmt::fmt)
target_compile_definitions(tidy_unittests PRIVATE UNITTESTS)
target_include_directories(tidy_unittests PRIVATE ../include ../../../include
                                                  ../../../tests/unittests)

add_test(NAME tidy_unittests COMMAND tidy_unittests)
