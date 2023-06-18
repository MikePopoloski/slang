# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(
        tidy_unittests
        ../../../tests/unittests/main.cpp ../../../tests/unittests/Test.cpp
        ../src/ASTHelperVisitors.cpp
        ../src/TidyConfig.cpp ../src/TidyConfigParser.cpp TidyConfigParserTest.cpp
        ../src/synthesis/OnlyAssignedOnReset.cpp OnlyAssignedOnResetTest.cpp
        ../src/synthesis/RegisterHasNoReset.cpp RegisterHasNoResetTest.cpp
        ../src/synthesis/NoLatchesOnDesign.cpp NoLatchesOnDesignTest.cpp
        ../src/style/EnforcePortSuffix.cpp EnforcePortSuffixTest.cpp
        ../src/style/NoOldAlwaysSyntax.cpp NoOldAlwaysSyntaxTest.cpp
        ../src/style/AlwaysCombNonBlocking.cpp AlwaysCombNonBlockingTest.cpp
        ../src/style/AlwaysFFBlocking.cpp AlwaysFFBlockingTest.cpp)

target_link_libraries(tidy_unittests PRIVATE slang::slang Catch2::Catch2
        fmt::fmt)
target_compile_definitions(tidy_unittests PRIVATE UNITTESTS)
target_include_directories(tidy_unittests PRIVATE ../include ../../../include
        ../../../tests/unittests)

add_test(NAME tidy_unittests COMMAND tidy_unittests)
