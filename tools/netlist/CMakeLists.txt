# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~
add_executable(slang_netlist netlist.cpp)
add_executable(slang::netlist ALIAS slang_netlist)

target_link_libraries(
  slang_netlist
  PRIVATE slang::slang
  PUBLIC ${SLANG_LIBRARIES})
target_include_directories(slang_netlist PRIVATE include ../../include)
set_target_properties(slang_netlist PROPERTIES OUTPUT_NAME "slang-netlist")

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_netlist RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()

if(SLANG_INCLUDE_TESTS)
  add_subdirectory(tests)
endif()
