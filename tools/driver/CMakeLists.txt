# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(slang_driver slang_main.cpp)
add_executable(slang::driver ALIAS slang_driver)

target_link_libraries(slang_driver PRIVATE slang::slang)
set_target_properties(slang_driver PROPERTIES OUTPUT_NAME "slang")

if(SLANG_FUZZ_TARGET)
  message("Tweaking driver for fuzz testing")
  target_compile_definitions(slang_driver PRIVATE FUZZ_TARGET)

  target_compile_options(slang_driver PRIVATE "-fsanitize=fuzzer")
  target_link_libraries(slang_driver PRIVATE "-fsanitize=fuzzer")
endif()

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_driver RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(slang_driver
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()
