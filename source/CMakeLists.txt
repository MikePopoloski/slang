# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# Helper function that defines library targets
function(slang_define_lib libname)
  target_compile_options(${libname} PRIVATE ${SLANG_WARN_FLAGS})
  target_compile_definitions(${libname} PUBLIC $<$<CONFIG:Debug>:DEBUG>)

  target_include_directories(
    ${libname}
    PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../include/>"
           "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>")
  target_include_directories(
    ${libname} PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}>"
                      "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>")
  target_include_directories(
    ${libname} SYSTEM
    PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../external/>")

  if(SLANG_INCLUDE_INSTALL)
    install(
      TARGETS ${libname}
      EXPORT ${SLANG_EXPORT_NAME}
      LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
      ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
      INCLUDES
      DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
  endif()

  if(SLANG_INCLUDE_PYLIB)
    set_target_properties(${libname} PROPERTIES POSITION_INDEPENDENT_CODE ON)
  endif()

  if(SLANG_CLANG_TIDY)
    set_target_properties(${libname} PROPERTIES CXX_CLANG_TIDY
                                                ${SLANG_CLANG_TIDY})
  endif()
endfunction()

# -------- Core library - depended on by everything else

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

# Generate version header
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/util/Version.cpp.in
               ${CMAKE_CURRENT_BINARY_DIR}/Version.cpp @ONLY)

set(slangcore_SOURCES
    ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/AllDiags.h
    diagnostics/DiagnosticClient.cpp
    diagnostics/DiagnosticEngine.cpp
    diagnostics/Diagnostics.cpp
    diagnostics/TextDiagnosticClient.cpp
    numeric/ConstantValue.cpp
    numeric/SVInt.cpp
    numeric/Time.cpp
    text/CharInfo.cpp
    text/Json.cpp
    text/SFormat.cpp
    text/SourceManager.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/Version.cpp
    util/Assert.cpp
    util/BumpAllocator.cpp
    util/CommandLine.cpp
    util/OS.cpp
    util/String.cpp)

if(NOT SLANG_USE_SYSTEM_LIBS)
  set(slangcore_SOURCES ${slangcore_SOURCES} ../external/xxHash/xxhash.c)

  set_source_files_properties(../external/xxHash/xxhash.c PROPERTIES LANGUAGE
                                                                     CXX)
  if(NOT CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
    set_source_files_properties(../external/xxHash/xxhash.c
                                PROPERTIES COMPILE_FLAGS -w)
  endif()
endif()

add_library(slangcore ${slangcore_SOURCES})
slang_define_lib(slangcore)

target_link_libraries(slangcore PUBLIC fmt::fmt)
if(SLANG_USE_SYSTEM_LIBS)
  find_package(fmt)
  find_package(xxHash)
  target_link_libraries(slangcore PRIVATE xxHash::xxhash)
else()
  if(SLANG_INCLUDE_PYLIB)
    set_target_properties(fmt PROPERTIES POSITION_INDEPENDENT_CODE ON)
  endif()
endif()

find_package(Threads)
target_link_libraries(slangcore PRIVATE ${CMAKE_THREAD_LIBS_INIT})

# -------- Parsing / syntax library

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

add_library(
  slangparser
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
  ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/TokenKind.cpp
  syntax/SyntaxFacts.cpp
  syntax/SyntaxNode.cpp
  syntax/SyntaxPrinter.cpp
  syntax/SyntaxTree.cpp
  syntax/SyntaxVisitor.cpp)
slang_define_lib(slangparser)
add_dependencies(slangparser slangcore)
target_link_libraries(slangparser PUBLIC slangcore)

# -------- Compiler library
add_library(
  slangcompiler
  ast/builtins/ArrayMethods.cpp
  ast/builtins/ConversionFuncs.cpp
  ast/builtins/CoverageFuncs.cpp
  ast/builtins/EnumMethods.cpp
  ast/builtins/GateTypes.cpp
  ast/builtins/MathFuncs.cpp
  ast/builtins/MiscSystemFuncs.cpp
  ast/builtins/NonConstFuncs.cpp
  ast/builtins/QueryFuncs.cpp
  ast/builtins/StdPackage.cpp
  ast/builtins/StringMethods.cpp
  ast/builtins/SystemTasks.cpp
  ast/expressions/AssertionExpr.cpp
  ast/expressions/AssignmentExpressions.cpp
  ast/expressions/CallExpression.cpp
  ast/expressions/LiteralExpressions.cpp
  ast/expressions/MiscExpressions.cpp
  ast/expressions/OperatorExpressions.cpp
  ast/expressions/SelectExpressions.cpp
  ast/symbols/AttributeSymbol.cpp
  ast/symbols/BlockSymbols.cpp
  ast/symbols/ClassSymbols.cpp
  ast/symbols/CompilationUnitSymbols.cpp
  ast/symbols/CoverSymbols.cpp
  ast/symbols/InstanceSymbols.cpp
  ast/symbols/MemberSymbols.cpp
  ast/symbols/ParameterBuilder.cpp
  ast/symbols/ParameterSymbols.cpp
  ast/symbols/PortSymbols.cpp
  ast/symbols/SubroutineSymbols.cpp
  ast/symbols/SymbolBuilders.cpp
  ast/symbols/ValueSymbol.cpp
  ast/symbols/VariableSymbols.cpp
  ast/types/AllTypes.cpp
  ast/types/DeclaredType.cpp
  ast/types/NetType.cpp
  ast/types/TypePrinter.cpp
  ast/types/Type.cpp
  ast/ASTContext.cpp
  ast/ASTSerializer.cpp
  ast/Bitstream.cpp
  ast/Compilation.cpp
  ast/Constraints.cpp
  ast/Definition.cpp
  ast/EvalContext.cpp
  ast/Expression.cpp
  ast/FormatHelpers.cpp
  ast/Lookup.cpp
  ast/LValue.cpp
  ast/Patterns.cpp
  ast/Scope.cpp
  ast/ScriptSession.cpp
  ast/SemanticFacts.cpp
  ast/SemanticModel.cpp
  ast/Statements.cpp
  ast/Symbol.cpp
  ast/SystemSubroutine.cpp
  ast/TimingControl.cpp
  driver/Driver.cpp)
slang_define_lib(slangcompiler)
add_dependencies(slangcompiler slangparser)
target_link_libraries(slangcompiler PUBLIC slangparser)

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
endif()
