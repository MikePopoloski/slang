# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(slang_hier hier.cpp)
add_executable(slang::hier ALIAS slang_hier)

target_link_libraries(slang_hier PRIVATE slang::slang)
set_target_properties(slang_hier PROPERTIES OUTPUT_NAME "slang-hier")

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(slang_hier
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_hier RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()
