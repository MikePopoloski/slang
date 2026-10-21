# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(
  reflect_unittests ../../../tests/unittests/main.cpp
                    ../../../tests/unittests/Test.cpp ReflectTest.cpp)

target_link_libraries(reflect_unittests PRIVATE Catch2::Catch2
                                                slang_reflect_obj_lib)
target_compile_definitions(reflect_unittests PRIVATE UNITTESTS)
target_include_directories(reflect_unittests PRIVATE ../../../tests/unittests)

target_compile_definitions(reflect_unittests
                           PRIVATE "TEST_DATA_DIR=\"${TEST_DATA_DEST}/\"")

add_test(NAME reflect_unittests COMMAND reflect_unittests)

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(reflect_unittests
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()
