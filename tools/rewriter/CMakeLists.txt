# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(rewriter rewriter.cpp)
target_link_libraries(rewriter PRIVATE slang::slang)

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(rewriter PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()
