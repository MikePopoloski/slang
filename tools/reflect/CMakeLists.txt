# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_library(
  slang_reflect_obj_lib OBJECT
  src/SvStruct.cpp src/SvType.cpp src/SvEnum.cpp src/SvTypeReflector.cpp
  src/SvLocalParam.cpp src/SvUnion.cpp)

target_include_directories(slang_reflect_obj_lib PUBLIC include)
target_link_libraries(slang_reflect_obj_lib PUBLIC slang::slang)

add_executable(slang_reflect src/reflect.cpp)
add_executable(slang::reflect ALIAS slang_reflect)

target_link_libraries(slang_reflect PRIVATE slang_reflect_obj_lib)
set_target_properties(slang_reflect PROPERTIES OUTPUT_NAME "slang-reflect")

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(slang_reflect
                 PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_reflect RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()
