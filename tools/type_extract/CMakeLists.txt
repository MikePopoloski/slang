# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_library(
  slang_type_extract_obj_lib OBJECT src/SvStruct.cpp src/SvType.cpp
                                    src/SvEnum.cpp src/SvTypeExtractor.cpp)

target_include_directories(slang_type_extract_obj_lib PUBLIC include
                                                             ../../include)
target_link_libraries(slang_type_extract_obj_lib PUBLIC slang::slang)

add_executable(slang_type_extract src/TypeExtract.cpp)
add_executable(slang::type_extract ALIAS slang_type_extract)

target_link_libraries(slang_type_extract PRIVATE slang_type_extract_obj_lib)
set_target_properties(slang_type_extract PROPERTIES OUTPUT_NAME
                                                    "slang-type-extract")

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS slang_type_extract
          RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()
