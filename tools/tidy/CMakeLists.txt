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
  src/style/OnlyANSIPortDecl.cpp
  src/synthesis/XilinxDoNotCareValues.cpp
  src/synthesis/CastSignedIndex.cpp
  src/style/NoDotStarInPortConnection.cpp
  src/style/NoImplicitPortNameInPortConnection.cpp
  src/style/AlwaysCombNamed.cpp
  src/style/GenerateNamed.cpp
  src/style/NoDotVarInPortConnection.cpp
  src/style/NoLegacyGenerate.cpp
  src/synthesis/AlwaysFFAssignmentOutsideConditional.cpp
  src/synthesis/UnusedSensitiveSignal.cpp)

target_include_directories(slang_tidy_obj_lib PUBLIC include)
target_link_libraries(slang_tidy_obj_lib PUBLIC slang::slang)

add_executable(slang_tidy src/tidy.cpp)
add_executable(slang::tidy ALIAS slang_tidy)

target_link_libraries(slang_tidy PRIVATE slang_tidy_obj_lib)
set_target_properties(slang_tidy PROPERTIES OUTPUT_NAME "slang-tidy")

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(slang_tidy
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_tidy RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()

if(SLANG_INCLUDE_TESTS)
  add_subdirectory(tests)
endif()
