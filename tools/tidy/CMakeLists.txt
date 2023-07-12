# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_library(
  slang_tidy_obj_lib OBJECT
  src/TidyConfig.cpp
  src/TidyConfigParser.cpp
  src/ASTHelperVisitors.cpp
  src/synthesis/OnlyAssignedOnReset.cpp
  src/synthesis/RegisterHasNoReset.cpp
  src/style/EnforcePortSuffix.cpp
  src/synthesis/NoLatchesOnDesign.cpp
  src/style/NoOldAlwaysSyntax.cpp
  src/style/AlwaysCombNonBlocking.cpp
  src/style/AlwaysFFBlocking.cpp
  src/style/EnforceModuleInstantiationPrefix.cpp
  src/style/OnlyANSIPortDecl.cpp)

target_include_directories(slang_tidy_obj_lib PUBLIC include ../../include)
target_link_libraries(slang_tidy_obj_lib PUBLIC slang::slang)

add_executable(slang_tidy src/tidy.cpp)
add_executable(slang::tidy ALIAS slang_tidy)

target_link_libraries(slang_tidy PRIVATE slang_tidy_obj_lib)
set_target_properties(slang_tidy PROPERTIES OUTPUT_NAME "slang-tidy")

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_tidy RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()

if(SLANG_INCLUDE_TESTS)
  add_subdirectory(tests)
endif()
