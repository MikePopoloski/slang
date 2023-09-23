# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(
  netlist_unittests
  ../../../tests/unittests/main.cpp
  ../../../tests/unittests/Test.cpp
  ../source/Netlist.cpp
  DepthFirstSearchTests.cpp
  DirectedGraphTests.cpp
  NameTests.cpp
  PathTests.cpp
  VariableSelectorsTests.cpp)

target_link_libraries(
  netlist_unittests
  PRIVATE slang::slang Catch2::Catch2
  PUBLIC ${SLANG_LIBRARIES})

target_compile_definitions(netlist_unittests PRIVATE UNITTESTS)

target_include_directories(
  netlist_unittests PRIVATE ../include ../../../include
                            ../../../tests/unittests)

add_test(NAME netlist_unittests COMMAND netlist_unittests)

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(netlist_unittests
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()
