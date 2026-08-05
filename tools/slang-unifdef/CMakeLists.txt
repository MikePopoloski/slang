# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(slang_unifdef slang_unifdef.cpp SimplifyingPreprocessor.cpp)
add_executable(slang::unifdef ALIAS slang_unifdef)

target_link_libraries(slang_unifdef PRIVATE slang::slang fmt::fmt)
set_target_properties(slang_unifdef PROPERTIES OUTPUT_NAME "slang-unifdef")

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(slang_unifdef
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_unifdef RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()

if(SLANG_INCLUDE_TESTS)
  add_subdirectory(test)
endif()
