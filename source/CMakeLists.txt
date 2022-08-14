# Helper function that defines library targets
function(slang_define_lib libname)
  target_compile_options(${libname} PRIVATE ${SLANG_WARN_FLAGS})
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

  if(SLANG_RUN_CLANG_TIDY)
    set_target_properties(${libname} PROPERTIES CXX_CLANG_TIDY clang-tidy)
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

if(NOT CMAKE_CXX_COMPILER_ID MATCHES "MSVC" AND NOT APPLE)
  # Link against C++17 filesystem
  if((CMAKE_CXX_COMPILER_ID MATCHES "GNU" AND CMAKE_CXX_COMPILER_VERSION
                                              VERSION_LESS 9.1)
     OR (CMAKE_CXX_COMPILER_ID MATCHES "Clang" AND CMAKE_CXX_COMPILER_VERSION
                                                   VERSION_LESS 9.0))
    target_link_libraries(slangcore PRIVATE stdc++fs)
  endif()
endif()

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
  binding/AssertionExpr.cpp
  binding/AssignmentExpressions.cpp
  binding/Bitstream.cpp
  binding/CallExpression.cpp
  binding/Constraints.cpp
  binding/BindContext.cpp
  binding/EvalContext.cpp
  binding/Expression.cpp
  binding/FormatHelpers.cpp
  binding/LiteralExpressions.cpp
  binding/Lookup.cpp
  binding/LValue.cpp
  binding/MiscExpressions.cpp
  binding/OperatorExpressions.cpp
  binding/Patterns.cpp
  binding/SelectExpressions.cpp
  binding/Statements.cpp
  binding/SystemSubroutine.cpp
  binding/TimingControl.cpp
  compilation/builtins/ArrayMethods.cpp
  compilation/builtins/ConversionFuncs.cpp
  compilation/builtins/CoverageFuncs.cpp
  compilation/builtins/EnumMethods.cpp
  compilation/builtins/GateTypes.cpp
  compilation/builtins/MathFuncs.cpp
  compilation/builtins/MiscSystemFuncs.cpp
  compilation/builtins/NonConstFuncs.cpp
  compilation/builtins/QueryFuncs.cpp
  compilation/builtins/StdPackage.cpp
  compilation/builtins/StringMethods.cpp
  compilation/builtins/SystemTasks.cpp
  compilation/Compilation.cpp
  compilation/Definition.cpp
  compilation/ScriptSession.cpp
  compilation/SemanticModel.cpp
  driver/Driver.cpp
  mir/Instr.cpp
  mir/MIRBuilder.cpp
  mir/MIRPrinter.cpp
  mir/Procedure.cpp
  symbols/ASTSerializer.cpp
  symbols/AttributeSymbol.cpp
  symbols/BlockSymbols.cpp
  symbols/ClassSymbols.cpp
  symbols/CompilationUnitSymbols.cpp
  symbols/CoverSymbols.cpp
  symbols/InstanceSymbols.cpp
  symbols/MemberSymbols.cpp
  symbols/ParameterBuilder.cpp
  symbols/ParameterSymbols.cpp
  symbols/PortSymbols.cpp
  symbols/Scope.cpp
  symbols/SemanticFacts.cpp
  symbols/SubroutineSymbols.cpp
  symbols/Symbol.cpp
  symbols/SymbolBuilders.cpp
  symbols/ValueSymbol.cpp
  symbols/VariableSymbols.cpp
  types/AllTypes.cpp
  types/DeclaredType.cpp
  types/NetType.cpp
  types/TypePrinter.cpp
  types/Type.cpp)
slang_define_lib(slangcompiler)
add_dependencies(slangcompiler slangparser)
target_link_libraries(slangcompiler PUBLIC slangparser)

# -------- Runtime library
add_library(slangruntime runtime/SimIO.cpp runtime/Runtime.cpp)
slang_define_lib(slangruntime)
add_dependencies(slangruntime slangcore)
target_link_libraries(slangruntime PUBLIC slangcore)

# -------- Codegen library
if(SLANG_INCLUDE_LLVM)
  add_library(
    slangcodegen
    codegen/CGExpr.cpp codegen/CGSysCall.cpp codegen/CodeGenerator.cpp
    codegen/CodeGenFunction.cpp codegen/CodeGenTypes.cpp codegen/JIT.cpp)
  slang_define_lib(slangcodegen)
  add_dependencies(slangcodegen slangparser)
  target_link_libraries(slangcodegen PUBLIC slangcompiler)

  find_package(LLVM REQUIRED CONFIG)

  message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
  message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
  target_include_directories(slangcodegen SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})

  llvm_map_components_to_libnames(llvm_libs support core orcjit native
                                  nativecodegen)
  target_link_libraries(slangcodegen PRIVATE ${llvm_libs})
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
endif()
