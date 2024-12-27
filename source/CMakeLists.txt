# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# -------- Generate code

# Generate diagnostic headers
add_custom_command(
  COMMAND
    ${Python_EXECUTABLE} ${SCRIPTS_DIR}/diagnostic_gen.py --outDir
    ${CMAKE_CURRENT_BINARY_DIR} --srcDir ${CMAKE_CURRENT_SOURCE_DIR} --incDir
    ${CMAKE_CURRENT_SOURCE_DIR}/../include/slang --diagnostics
    ${SCRIPTS_DIR}/diagnostics.txt
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/AllDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/CompilationDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/ConstEvalDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/DeclarationsDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/ExpressionsDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/GeneralDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/LexerDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/LookupDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/MetaDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/NumericDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/ParserDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/PreprocessorDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/StatementsDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/SysFuncsDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/TypesDiags.h
         ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
  DEPENDS ${SCRIPTS_DIR}/diagnostic_gen.py ${SCRIPTS_DIR}/diagnostics.txt
  COMMENT "Generating diagnostics")

# Generate syntax headers and sources
add_custom_command(
  COMMAND ${Python_EXECUTABLE} ${SCRIPTS_DIR}/syntax_gen.py --dir
          ${CMAKE_CURRENT_BINARY_DIR} --syntax ${SCRIPTS_DIR}/syntax.txt
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h
         ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/SyntaxClone.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxFwd.h
         ${CMAKE_CURRENT_BINARY_DIR}/slang/parsing/TokenKind.h
         ${CMAKE_CURRENT_BINARY_DIR}/TokenKind.cpp
  DEPENDS ${SCRIPTS_DIR}/syntax_gen.py ${SCRIPTS_DIR}/syntax.txt
          ${SCRIPTS_DIR}/triviakinds.txt ${SCRIPTS_DIR}/tokenkinds.txt
  COMMENT "Generating syntax")

# Generate version header
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/util/VersionInfo.cpp.in
               ${CMAKE_CURRENT_BINARY_DIR}/VersionInfo.cpp @ONLY)

# -------- Primary library target
add_library(
  slang_slang
  ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/SyntaxClone.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/TokenKind.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/VersionInfo.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/AllDiags.h
  diagnostics/DiagnosticClient.cpp
  diagnostics/DiagnosticEngine.cpp
  diagnostics/Diagnostics.cpp
  diagnostics/JsonDiagnosticClient.cpp
  diagnostics/TextDiagnosticClient.cpp
  driver/Driver.cpp
  driver/SourceLoader.cpp
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
  parsing/ParserMetadata.cpp
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
  text/Glob.cpp
  text/Json.cpp
  text/SourceLocation.cpp
  text/SourceManager.cpp
  util/BumpAllocator.cpp
  util/CommandLine.cpp
  util/IntervalMap.cpp
  util/OS.cpp
  util/SmallVector.cpp
  util/String.cpp
  util/TimeTrace.cpp
  util/Util.cpp)

add_subdirectory(ast)

add_library(slang::slang ALIAS slang_slang)
set_target_properties(
  slang_slang
  PROPERTIES CXX_VISIBILITY_PRESET hidden
             VISIBILITY_INLINES_HIDDEN YES
             VERSION ${PROJECT_VERSION}
             SOVERSION ${PROJECT_VERSION_MAJOR}
             EXPORT_NAME slang
             OUTPUT_NAME ${SLANG_LIB_NAME})

# Compile options
target_compile_options(slang_slang PRIVATE ${SLANG_WARN_FLAGS})
target_compile_definitions(slang_slang PUBLIC $<$<CONFIG:Debug>:DEBUG>)

# Include directories
target_include_directories(
  slang_slang
  PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../include/>"
         "$<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}>"
         "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>")
target_include_directories(
  slang_slang SYSTEM
  PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../external/>")

# Link libraries
find_package(Threads)
target_link_libraries(slang_slang PUBLIC fmt::fmt Boost::headers
                                         ${CMAKE_THREAD_LIBS_INIT})

if(SLANG_USE_MIMALLOC)
  target_link_libraries(slang_slang PUBLIC ${mimalloc_target})
  target_compile_definitions(slang_slang PUBLIC SLANG_USE_MIMALLOC)
endif()

# If building the Python library we'll end up with a shared lib no matter what,
# so make sure we always build with PIC.
if(SLANG_INCLUDE_PYLIB)
  set_target_properties(slang_slang PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()

# Run clang-tidy if desired. This is a separate project-specific variable so
# that it can apply just to the project itself and not any dependencies.
if(SLANG_CLANG_TIDY)
  set_target_properties(slang_slang PROPERTIES CXX_CLANG_TIDY
                                               ${SLANG_CLANG_TIDY})
endif()

# Set the magic _STATIC_DEFINE definition to assist with building combo static
# and shared libs in the same build.
if(NOT BUILD_SHARED_LIBS)
  target_compile_definitions(slang_slang PUBLIC SLANG_STATIC_DEFINE)
endif()

# For the generated export header, suppress annoying warnings
set(suppress_export_warnings
    "
#if defined(_MSC_VER) && !defined(__ICL)
  #pragma warning(disable:4251)
  #pragma warning(disable:4275)
#elif defined(__GNUC__) && !defined(__clang__)
  #pragma GCC diagnostic ignored \"-Wattributes\"
#endif
")

include(GenerateExportHeader)
generate_export_header(
  slang_slang
  BASE_NAME
  slang
  EXPORT_FILE_NAME
  ${CMAKE_CURRENT_BINARY_DIR}/slang/slang_export.h
  CUSTOM_CONTENT_FROM_VARIABLE
  suppress_export_warnings)

# Installation rules for headers.
if(SLANG_INCLUDE_INSTALL)
  install(
    DIRECTORY ../include/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
    COMPONENT slang_Development)
  install(
    DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/slang/diagnostics
    COMPONENT slang_Development)
  install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h
          ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
          ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxFwd.h
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/slang/syntax/
    COMPONENT slang_Development)
  install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/parsing/TokenKind.h
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/slang/parsing/
    COMPONENT slang_Development)
  install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/slang_export.h
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/slang/
    COMPONENT slang_Development)
endif()
