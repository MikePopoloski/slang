# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

if(SLANG_INCLUDE_LLVM)
  # Compile the C helper needed by sv_lib_roundtrip.sv into a native object
  # file. Using an OBJECT library lets CMake choose the right output extension
  # for the current platform (.o on Unix, .obj on Windows/MSVC).
  add_library(sv_lib_roundtrip OBJECT sv_lib_roundtrip.cpp)

  add_test(
    NAME codegen_ir_tests
    COMMAND
      ${Python_EXECUTABLE} ${PROJECT_SOURCE_DIR}/scripts/slang-lit.py
      ${CMAKE_CURRENT_LIST_DIR} --slang $<TARGET_FILE:slang_driver> --no-color
      --define sv_lib_helper_o=$<TARGET_OBJECTS:sv_lib_roundtrip>)
endif()
