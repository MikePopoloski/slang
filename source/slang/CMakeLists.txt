SET(SCRIPTS_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../scripts)

add_custom_command(
    COMMAND ${Python_EXECUTABLE} ${SCRIPTS_DIR}/diagnostic_gen.py
                --outDir ${CMAKE_CURRENT_BINARY_DIR}
                --srcDir ${CMAKE_CURRENT_SOURCE_DIR}
                --incDir ${CMAKE_CURRENT_SOURCE_DIR}/../../include/slang
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/AllDiags.h ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
    DEPENDS ${SCRIPTS_DIR}/diagnostic_gen.py ${SCRIPTS_DIR}/diagnostics.txt
    COMMENT "Generating diagnostics"
)

add_custom_command(
    COMMAND ${Python_EXECUTABLE} ${SCRIPTS_DIR}/syntax_gen.py --dir ${CMAKE_CURRENT_BINARY_DIR}
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
    DEPENDS ${SCRIPTS_DIR}/syntax_gen.py ${SCRIPTS_DIR}/syntax.txt
    COMMENT "Generating syntax"
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
    -P "${CMAKE_CURRENT_SOURCE_DIR}/../../cmake/gitversion.cmake"
)

add_library(slang
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

    ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
    diagnostics/DiagnosticClient.cpp
    diagnostics/DiagnosticEngine.cpp
    diagnostics/Diagnostics.cpp
    diagnostics/TextDiagnosticClient.cpp

    mir/Instr.cpp
    mir/MIRBuilder.cpp
    mir/MIRPrinter.cpp
    mir/Procedure.cpp

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
    parsing/Token.cpp

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

    ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp
    syntax/SyntaxFacts.cpp
    syntax/SyntaxNode.cpp
    syntax/SyntaxPrinter.cpp
    syntax/SyntaxTree.cpp
    syntax/SyntaxVisitor.cpp

    text/Json.cpp
    text/SFormat.cpp
    text/SourceManager.cpp

    ${CMAKE_CURRENT_BINARY_DIR}/Version.cpp
    util/Assert.cpp
    util/BumpAllocator.cpp
    util/CommandLine.cpp
    util/Hash.cpp
    util/OS.cpp
    util/String.cpp
)

if(SLANG_INCLUDE_LLVM)
    target_sources(slang PRIVATE
        codegen/CodeGenerator.cpp
        codegen/ExpressionEmitter.cpp
        codegen/JIT.cpp
        codegen/StatementEmitter.cpp
        codegen/SystemCallEmitter.cpp
    )
endif()

add_dependencies(slang gen_version)

target_compile_options(slang PRIVATE ${SLANG_WARN_FLAGS})

if(NOT CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
    # Link against C++17 filesystem
    target_link_libraries(slang PUBLIC stdc++fs)
endif()

target_link_libraries(slang PRIVATE CONAN_PKG::fmt)
target_link_libraries(slang PRIVATE simrt)

find_package(Threads)
target_link_libraries(slang PUBLIC ${CMAKE_THREAD_LIBS_INIT})

target_include_directories(slang PUBLIC ../../include/)
target_include_directories(slang PUBLIC ${CMAKE_CURRENT_BINARY_DIR})
target_include_directories(slang SYSTEM PUBLIC ../../external/)

if(SLANG_INCLUDE_LLVM)
    find_package(LLVM REQUIRED CONFIG)

    message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
    message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
    target_include_directories(slang SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
    target_compile_options(slang PRIVATE ${LLVM_DEFINITIONS})

    llvm_map_components_to_libnames(llvm_libs support core orcjit native nativecodegen)
    target_link_libraries(slang PRIVATE ${llvm_libs})
endif()

install(TARGETS slang
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib)
install(DIRECTORY ../../include/ DESTINATION include)
install(DIRECTORY ../../external/ DESTINATION include)
install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/ DESTINATION include/slang/diagnostics)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h DESTINATION include/slang/syntax/)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h DESTINATION include/slang/syntax/)