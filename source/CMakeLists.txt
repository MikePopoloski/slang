SET(SCRIPTS_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../scripts)

function(slang_define_lib libname)
    target_compile_options(${libname} PRIVATE ${SLANG_WARN_FLAGS})
    target_include_directories(${libname} PUBLIC ../include/)
    target_include_directories(${libname} PUBLIC ${CMAKE_CURRENT_BINARY_DIR})
    target_include_directories(${libname} SYSTEM PUBLIC ../external/)
    target_link_libraries(${libname} PUBLIC CONAN_PKG::fmt)
    install(TARGETS ${libname}
            LIBRARY DESTINATION lib
            ARCHIVE DESTINATION lib)
endfunction()

install(DIRECTORY ../include/ DESTINATION include)
install(DIRECTORY ../external/ DESTINATION include)
install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/ DESTINATION include/slang/diagnostics)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h DESTINATION include/slang/syntax/)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h DESTINATION include/slang/syntax/)

#-------- Core library - depended on by everything else
add_custom_command(
    COMMAND ${Python_EXECUTABLE} ${SCRIPTS_DIR}/diagnostic_gen.py
                --outDir ${CMAKE_CURRENT_BINARY_DIR}
                --srcDir ${CMAKE_CURRENT_SOURCE_DIR}
                --incDir ${CMAKE_CURRENT_SOURCE_DIR}/../include/slang
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/AllDiags.h ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
    DEPENDS ${SCRIPTS_DIR}/diagnostic_gen.py ${SCRIPTS_DIR}/diagnostics.txt
    COMMENT "Generating diagnostics"
)

add_custom_target(gen_version
    ALL
    BYPRODUCTS ${CMAKE_CURRENT_BINARY_DIR}/Version.cpp
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/util/Version.cpp.in
    COMMAND ${CMAKE_COMMAND}
    -Dinfile="${CMAKE_CURRENT_SOURCE_DIR}/util/Version.cpp.in"
    -Doutfile="${CMAKE_CURRENT_BINARY_DIR}/Version.cpp"
        -Dlocal_dir="${CMAKE_CURRENT_SOURCE_DIR}"
        -D_version_major=${SLANG_VERSION_MAJOR}
        -D_version_minor=${SLANG_VERSION_MINOR}
    -P "${CMAKE_CURRENT_SOURCE_DIR}/../cmake/gitversion.cmake"
)

add_library(slangcore
    ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
    diagnostics/DiagnosticClient.cpp
    diagnostics/DiagnosticEngine.cpp
    diagnostics/Diagnostics.cpp
    diagnostics/TextDiagnosticClient.cpp

    numeric/SVInt.cpp
    numeric/Time.cpp

    text/Json.cpp
    text/SourceManager.cpp

    ${CMAKE_CURRENT_BINARY_DIR}/Version.cpp
    util/Assert.cpp
    util/BumpAllocator.cpp
    util/CommandLine.cpp
    util/Hash.cpp
    util/OS.cpp
    util/String.cpp

    # TODO: remove this
    ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
)
slang_define_lib(slangcore)
add_dependencies(slangcore gen_version)

if(NOT CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
    # Link against C++17 filesystem
    target_link_libraries(slangcore PUBLIC stdc++fs)
endif()

find_package(Threads)
target_link_libraries(slangcore PUBLIC ${CMAKE_THREAD_LIBS_INIT})

#-------- Parsing / syntax library
add_custom_command(
    COMMAND ${Python_EXECUTABLE} ${SCRIPTS_DIR}/syntax_gen.py --dir ${CMAKE_CURRENT_BINARY_DIR}
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
    DEPENDS ${SCRIPTS_DIR}/syntax_gen.py ${SCRIPTS_DIR}/syntax.txt
    COMMENT "Generating syntax"
)

add_library(slangparser
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
    syntax/SyntaxFacts.cpp
    syntax/SyntaxNode.cpp
    syntax/SyntaxPrinter.cpp
    syntax/SyntaxTree.cpp
    syntax/SyntaxVisitor.cpp
)
slang_define_lib(slangparser)
add_dependencies(slangparser slangcore)
target_link_libraries(slangparser INTERFACE slangcore)

#-------- Compiler library
add_library(slangcompiler
    binding/AssignmentExpressions.cpp
    binding/BindContext.cpp
    binding/ConstantValue.cpp
    binding/EvalContext.cpp
    binding/Expression.cpp
    binding/LiteralExpressions.cpp
    binding/MiscExpressions.cpp
    binding/OperatorExpressions.cpp
    binding/PatternExpressions.cpp
    binding/Statements.cpp
    binding/SystemSubroutine.cpp
    binding/TimingControl.cpp

    compilation/builtins/ArrayMethods.cpp
    compilation/builtins/ConversionFuncs.cpp
    compilation/builtins/EnumMethods.cpp
    compilation/builtins/MathFuncs.cpp
    compilation/builtins/MiscSystemFuncs.cpp
    compilation/builtins/NonConstFuncs.cpp
    compilation/builtins/QueryFuncs.cpp
    compilation/builtins/StringMethods.cpp
    compilation/builtins/SystemTasks.cpp

    compilation/Compilation.cpp
    compilation/Definition.cpp
    compilation/InstanceCache.cpp
    compilation/ScriptSession.cpp
    compilation/SemanticModel.cpp
    compilation/SFormat.cpp

    symbols/AllTypes.cpp
    symbols/ASTSerializer.cpp
    symbols/AttributeSymbol.cpp
    symbols/BlockSymbols.cpp
    symbols/CompilationUnitSymbols.cpp
    symbols/DeclaredType.cpp
    symbols/InstanceSymbols.cpp
    symbols/Lookup.cpp
    symbols/MemberSymbols.cpp
    symbols/ParameterSymbols.cpp
    symbols/PortSymbols.cpp
    symbols/Scope.cpp
    symbols/SemanticFacts.cpp
    symbols/Symbol.cpp
    symbols/TypePrinter.cpp
    symbols/Type.cpp
    symbols/VariableSymbols.cpp
)
slang_define_lib(slangcompiler)
add_dependencies(slangcompiler slangcore)
target_link_libraries(slangcompiler INTERFACE slangparser)

#-------- MIR library
add_library(slangmir
    mir/Instr.cpp
    mir/MIRBuilder.cpp
    mir/MIRPrinter.cpp
    mir/Procedure.cpp
)
slang_define_lib(slangmir)
add_dependencies(slangmir slangcore)
target_link_libraries(slangmir INTERFACE slangcompiler)

#-------- Runtime library
add_library(slangruntime
    runtime/SimIO.cpp
    runtime/Runtime.cpp
)
slang_define_lib(slangruntime)
add_dependencies(slangruntime slangcore)
target_link_libraries(slangruntime INTERFACE slangcore)

#-------- Codegen library
if(SLANG_INCLUDE_LLVM)
    add_library(slangcodegen
        codegen/CodeGenerator.cpp
        codegen/ExpressionEmitter.cpp
        codegen/JIT.cpp
        codegen/StatementEmitter.cpp
        codegen/SystemCallEmitter.cpp
    )
    slang_define_lib(slangcodegen)
    add_dependencies(slangcodegen slangcore)
    target_link_libraries(slangcodegen INTERFACE slangmir)

    find_package(LLVM REQUIRED CONFIG)

    message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
    message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
    target_include_directories(slangcodegen SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
    target_compile_options(slangcodegen PRIVATE ${LLVM_DEFINITIONS})

    llvm_map_components_to_libnames(llvm_libs support core orcjit native nativecodegen)
    target_link_libraries(slangcodegen PRIVATE ${llvm_libs})
endif()