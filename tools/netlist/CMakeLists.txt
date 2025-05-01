# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(slang_netlist netlist.cpp source/Netlist.cpp
                             source/CombLoops.cpp)
add_executable(slang::netlist ALIAS slang_netlist)

target_link_libraries(slang_netlist PRIVATE slang::slang)
set_target_properties(slang_netlist PROPERTIES OUTPUT_NAME "slang-netlist")
target_include_directories(slang_netlist PRIVATE include)

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(slang_netlist
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_netlist RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()

if(SLANG_INCLUDE_TESTS)
  add_subdirectory(tests)
endif()
