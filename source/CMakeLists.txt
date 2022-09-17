# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# -------- Dependencies
find_package(Threads)
if(SLANG_USE_SYSTEM_LIBS)
  find_package(fmt)
  find_package(xxHash)
else()
  if(SLANG_INCLUDE_PYLIB)
    set_target_properties(fmt PROPERTIES POSITION_INDEPENDENT_CODE ON)
  endif()
endif()

# -------- Generate code

# Generate diagnostic headers
add_custom_command(
  COMMAND
    ${Python_EXECUTABLE} ${SCRIPTS_DIR}/diagnostic_gen.py --outDir
    ${CMAKE_CURRENT_BINARY_DIR} --srcDir ${CMAKE_CURRENT_SOURCE_DIR} --incDir
    ${CMAKE_CURRENT_SOURCE_DIR}/../include/slang
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/AllDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
  DEPENDS ${SCRIPTS_DIR}/diagnostic_gen.py ${SCRIPTS_DIR}/diagnostics.txt
  COMMENT "Generating diagnostics")

# Generate syntax headers and sources
add_custom_command(
  COMMAND ${Python_EXECUTABLE} ${SCRIPTS_DIR}/syntax_gen.py --dir
          ${CMAKE_CURRENT_BINARY_DIR}
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h
         ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/parsing/TokenKind.h
         ${CMAKE_CURRENT_BINARY_DIR}/TokenKind.cpp
  DEPENDS ${SCRIPTS_DIR}/syntax_gen.py ${SCRIPTS_DIR}/syntax.txt
          ${SCRIPTS_DIR}/triviakinds.txt ${SCRIPTS_DIR}/tokenkinds.txt
  COMMENT "Generating syntax")

# Generate version header
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/util/Version.cpp.in
               ${CMAKE_CURRENT_BINARY_DIR}/Version.cpp @ONLY)

# -------- Primary library target
add_library(
  slang
  ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/TokenKind.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/Version.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/AllDiags.h
  diagnostics/DiagnosticClient.cpp
  diagnostics/DiagnosticEngine.cpp
  diagnostics/Diagnostics.cpp
  diagnostics/TextDiagnosticClient.cpp
  driver/Driver.cpp
  numeric/ConstantValue.cpp
  numeric/SVInt.cpp
  numeric/Time.cpp
  parsing/Lexer.cpp
  parsing/LexerFacts.cpp
  parsing/NumberParser.cpp
  parsing/Parser.cpp
  parsing/Parser_expressions.cpp
  parsing/Parser_members.cpp
  parsing/Parser_statements.cpp
  parsing/ParserBase.cpp
  parsing/Preprocessor.cpp
  parsing/Preprocessor_macros.cpp
  parsing/Preprocessor_pragmas.cpp
  parsing/Token.cpp
  syntax/SyntaxFacts.cpp
  syntax/SyntaxNode.cpp
  syntax/SyntaxPrinter.cpp
  syntax/SyntaxTree.cpp
  syntax/SyntaxVisitor.cpp
  text/CharInfo.cpp
  text/Json.cpp
  text/SFormat.cpp
  text/SourceManager.cpp
  util/Assert.cpp
  util/BumpAllocator.cpp
  util/CommandLine.cpp
  util/OS.cpp
  util/String.cpp)

add_subdirectory(ast)

# Add xxhash source if we aren't linking to a system package.
if(SLANG_USE_SYSTEM_LIBS)
  target_link_libraries(slang PRIVATE xxHash::xxhash)
else()
  target_sources(slang PRIVATE ../external/xxHash/xxhash.c)
  set_source_files_properties(../external/xxHash/xxhash.c PROPERTIES LANGUAGE
                                                                     CXX)
  if(NOT CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
    set_source_files_properties(../external/xxHash/xxhash.c
                                PROPERTIES COMPILE_FLAGS -w)
  endif()
endif()

# Compile options
target_compile_options(slang PRIVATE ${SLANG_WARN_FLAGS})
target_compile_definitions(slang PUBLIC $<$<CONFIG:Debug>:DEBUG>)

# Include directories
target_include_directories(
  slang
  PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../include/>"
         "$<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}>"
         "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>")
target_include_directories(
  slang SYSTEM
  PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../external/>")

# Link libraries
target_link_libraries(slang PRIVATE ${CMAKE_THREAD_LIBS_INIT})
target_link_libraries(slang PUBLIC fmt::fmt)

# If building the Python library we'll end up with a shared lib no matter what,
# so make sure we always build with PIC.
if(SLANG_INCLUDE_PYLIB)
  set_target_properties(slang PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()

if(SLANG_CLANG_TIDY)
  set_target_properties(slang PROPERTIES CXX_CLANG_TIDY ${SLANG_CLANG_TIDY})
endif()

# Installation rules
if(SLANG_INCLUDE_INSTALL)
  install(DIRECTORY ../include/ DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
  install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/slang/diagnostics)
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/slang/syntax/)
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/slang/syntax/)
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/parsing/TokenKind.h
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/slang/parsing/)
  install(DIRECTORY ../external/ieee1800/
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/ieee1800)
  install(FILES ../external/flat_hash_map.hpp ../external/span.hpp
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

  if(NOT SLANG_USE_SYSTEM_LIBS)
    install(FILES ../external/xxHash/xxhash.h
            DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/xxhash)
  endif()

  install(
    TARGETS slang
    EXPORT ${SLANG_EXPORT_NAME}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    INCLUDES
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
endif()
