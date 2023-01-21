# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~
add_executable(slang_tidy tidy.cpp synthesis/OnlyAssignedOnReset.cpp
                          synthesis/RegisterHasNoReset.cpp)
add_executable(slang::tidy ALIAS slang_tidy)

target_link_libraries(
  slang_tidy
  PRIVATE slang::slang fmt::fmt
  PUBLIC ${SLANG_LIBRARIES})
target_include_directories(slang_tidy PRIVATE include ../../include)
set_target_properties(slang_tidy PROPERTIES OUTPUT_NAME "slang-tidy")

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_tidy RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()

add_subdirectory(tests)
