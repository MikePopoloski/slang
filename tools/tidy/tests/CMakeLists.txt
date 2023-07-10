# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(
  tidy_unittests
  ../../../tests/unittests/main.cpp
  ../../../tests/unittests/Test.cpp
  TidyConfigParserTest.cpp
  OnlyAssignedOnResetTest.cpp
  RegisterHasNoResetTest.cpp
  NoLatchesOnDesignTest.cpp
  EnforcePortSuffixTest.cpp
  NoOldAlwaysSyntaxTest.cpp
  AlwaysCombNonBlockingTest.cpp
  AlwaysFFBlockingTest.cpp
  EnforceModuleInstantiationTest.cpp
  OnlyANSIPortDecl.cpp)

target_link_libraries(tidy_unittests PRIVATE Catch2::Catch2 slang_tidy_obj_lib)
target_compile_definitions(tidy_unittests PRIVATE UNITTESTS)
target_include_directories(tidy_unittests PRIVATE ../../../tests/unittests)

add_test(NAME tidy_unittests COMMAND tidy_unittests)
