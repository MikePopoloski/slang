SET(SCRIPTS_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../scripts)

function(slang_define_lib libname)
    target_compile_options(${libname} PRIVATE ${SLANG_WARN_FLAGS})
    target_include_directories(${libname} PUBLIC ../include/)
    target_include_directories(${libname} PUBLIC ${CMAKE_CURRENT_BINARY_DIR})
    target_include_directories(${libname} SYSTEM PUBLIC ../external/)
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

    numeric/ConstantValue.cpp
    numeric/SVInt.cpp
    numeric/Time.cpp

    text/Json.cpp
    text/SFormat.cpp
    text/SourceManager.cpp

    ${CMAKE_CURRENT_BINARY_DIR}/Version.cpp
    util/Assert.cpp
    util/BumpAllocator.cpp
    util/CommandLine.cpp
    util/OS.cpp
    util/String.cpp

    ../external/fmt/format.cc
    ../external/fmt/os.cc
    ../external/xxhash/xxhash.cpp
)
slang_define_lib(slangcore)
add_dependencies(slangcore gen_version)

if(NOT CMAKE_CXX_COMPILER_ID MATCHES "MSVC" AND NOT APPLE)
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
    binding/PatternExpressions.cpp
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
    compilation/DesignTree.cpp
    compilation/InstanceCache.cpp
    compilation/ScriptSession.cpp
    compilation/SemanticModel.cpp

    mir/Instr.cpp
    mir/MIRBuilder.cpp
    mir/MIRPrinter.cpp
    mir/Procedure.cpp

    symbols/ASTSerializer.cpp
    symbols/AttributeSymbol.cpp
    symbols/BlockSymbols.cpp
    symbols/ClassSymbols.cpp
    symbols/CompilationUnitSymbols.cpp
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
    types/Type.cpp
)
slang_define_lib(slangcompiler)
add_dependencies(slangcompiler slangparser)
target_link_libraries(slangcompiler INTERFACE slangparser)

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
        codegen/CGExpr.cpp
        codegen/CGSysCall.cpp
        codegen/CodeGenerator.cpp
        codegen/CodeGenFunction.cpp
        codegen/CodeGenTypes.cpp
        codegen/JIT.cpp
    )
    slang_define_lib(slangcodegen)
    add_dependencies(slangcodegen slangparser)
    target_link_libraries(slangcodegen INTERFACE slangcompiler)

    find_package(LLVM REQUIRED CONFIG)

    message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
    message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
    target_include_directories(slangcodegen SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})

    llvm_map_components_to_libnames(llvm_libs support core orcjit native nativecodegen)
    target_link_libraries(slangcodegen PRIVATE ${llvm_libs})
endif()
