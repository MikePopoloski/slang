# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(slang_threadtest threadtest.cpp)
add_executable(slang::threadtest ALIAS slang_threadtest)

target_link_libraries(slang_threadtest PRIVATE slang::slang)

set_target_properties(slang_threadtest PROPERTIES OUTPUT_NAME
                                                  "slang-threadtest")

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(slang_threadtest
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang" OR CMAKE_CXX_COMPILER_ID STREQUAL
                                             "GNU")
  string(FIND "${CMAKE_CXX_FLAGS}" "fsanitize" found)
  if(found EQUAL -1)
    target_compile_options(slang_threadtest PRIVATE "-fsanitize=thread")
    target_link_libraries(slang_threadtest PRIVATE "-fsanitize=thread")
  endif()
endif()
