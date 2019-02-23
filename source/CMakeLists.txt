add_custom_command(
	COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/diagnostic_gen.py --dir ${CMAKE_CURRENT_BINARY_DIR}
	OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/DiagCode.h ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
	DEPENDS ../scripts/diagnostic_gen.py ../scripts/diagnostics.txt
	COMMENT "Generating diagnostics in ${CMAKE_CURRENT_BINARY_DIR} with ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}"
)

add_custom_command(
	COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/syntax_gen.py --dir ${CMAKE_CURRENT_BINARY_DIR}
	OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
	DEPENDS ../scripts/syntax_gen.py ../scripts/syntax.txt
	COMMENT "Generating syntax in ${CMAKE_CURRENT_BINARY_DIR}"
)

add_library(slang STATIC
	binding/BindContext.cpp
	binding/ConstantValue.cpp
	binding/EvalContext.cpp
	binding/Expressions.cpp
	binding/Expressions_eval.cpp
	binding/Statements.cpp

	compilation/BuiltInSubroutines.cpp
	compilation/Compilation.cpp
	compilation/ScriptSession.cpp
	compilation/SemanticModel.cpp

	${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
	diagnostics/Diagnostics.cpp
	diagnostics/DiagnosticWriter.cpp

	numeric/SVInt.cpp
	numeric/Time.cpp
	numeric/ValueConverter.cpp
	numeric/VectorBuilder.cpp

	parsing/Lexer.cpp
	parsing/LexerFacts.cpp
	parsing/Parser.cpp
	parsing/Parser_expressions.cpp
	parsing/Parser_statements.cpp
	parsing/ParserBase.cpp
	parsing/Preprocessor.cpp
	parsing/Token.cpp

	symbols/DeclaredType.cpp
	symbols/HierarchySymbols.cpp
	symbols/MemberSymbols.cpp
	symbols/Scope.cpp
	symbols/SemanticFacts.cpp
	symbols/StatementBodiedScope.cpp
	symbols/Symbol.cpp
	symbols/TypePrinter.cpp
	symbols/TypeSymbols.cpp

	${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp
	syntax/SyntaxFacts.cpp
	syntax/SyntaxNode.cpp
	syntax/SyntaxPrinter.cpp
	syntax/SyntaxTree.cpp
	syntax/SyntaxVisitor.cpp

	text/SourceManager.cpp

	util/BumpAllocator.cpp
	util/Hash.cpp
	util/Util.cpp
)

if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
	# Warnings as errors
	target_compile_options(slang PRIVATE /WX)
else()
	# Link against C++17 filesystem
	target_link_libraries(slang PUBLIC stdc++fs)
	target_compile_options(slang PRIVATE
		-Wall
		-Wextra
		-Werror
	)
endif()

if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
	target_compile_options(slang PRIVATE
		-Warray-bounds-pointer-arithmetic
		-Wassign-enum
		-Wbad-function-cast
		-Wcast-qual
		-Wcomma
		-Wduplicate-enum
		-Wduplicate-method-arg
		-Wimplicit-fallthrough
		-Wrange-loop-analysis
		-Wpedantic
		-Wconversion
		-Wshadow
		-Wno-missing-braces
	)
elseif (CMAKE_CXX_COMPILER_ID MATCHES "GNU")
	target_compile_options(slang PRIVATE
		-Wunused-value
		-Wformat-security
		-Wnull-dereference
		-Wimplicit-fallthrough=5
		-Walloc-zero
		-Wlogical-op
		-Wlogical-not-parentheses
		-Wvla
		-Wnoexcept
		-Wduplicated-cond
		-Wtype-limits
	)
endif()

target_link_libraries(slang PUBLIC CONAN_PKG::jsonformoderncpp)
target_link_libraries(slang PUBLIC CONAN_PKG::fmt)

target_include_directories(slang PUBLIC ../include/)
target_include_directories(slang PUBLIC ${CMAKE_CURRENT_BINARY_DIR})
target_include_directories(slang SYSTEM PUBLIC ../external/)
