add_custom_command(
	COMMAND ${Python_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/diagnostic_gen.py
				--outDir ${CMAKE_CURRENT_BINARY_DIR}
				--srcDir ${CMAKE_CURRENT_SOURCE_DIR}
				--incDir ${CMAKE_CURRENT_SOURCE_DIR}/../include/slang
	OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/diagnostics/AllDiags.h ${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
	DEPENDS ../scripts/diagnostic_gen.py ../scripts/diagnostics.txt
	COMMENT "Generating diagnostics"
)

add_custom_command(
	COMMAND ${Python_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/syntax_gen.py --dir ${CMAKE_CURRENT_BINARY_DIR}
	OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/AllSyntax.h ${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp ${CMAKE_CURRENT_BINARY_DIR}/slang/syntax/SyntaxKind.h
	DEPENDS ../scripts/syntax_gen.py ../scripts/syntax.txt
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
	-P "${CMAKE_CURRENT_SOURCE_DIR}/../cmake/gitversion.cmake"
)

add_library(slang
	binding/BindContext.cpp
	binding/ConstantValue.cpp
	binding/EvalContext.cpp
	binding/Expressions.cpp
	binding/Expressions_eval.cpp
	binding/Statements.cpp
	binding/SystemSubroutine.cpp
	binding/TimingControl.cpp

	compilation/builtins/ArrayMethods.cpp
	compilation/builtins/EnumMethods.cpp
	compilation/builtins/MathFuncs.cpp
	compilation/builtins/MiscSystemFuncs.cpp
	compilation/builtins/NonConstFuncs.cpp
	compilation/builtins/QueryFuncs.cpp
	compilation/builtins/StringMethods.cpp
	compilation/builtins/SystemTasks.cpp

	compilation/Compilation.cpp
	compilation/ScriptSession.cpp
	compilation/SemanticModel.cpp

	${CMAKE_CURRENT_BINARY_DIR}/DiagCode.cpp
	diagnostics/DiagnosticClient.cpp
	diagnostics/DiagnosticEngine.cpp
	diagnostics/Diagnostics.cpp
	diagnostics/TextDiagnosticClient.cpp

	numeric/SVInt.cpp
	numeric/Time.cpp
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
	symbols/Symbol.cpp
	symbols/TypePrinter.cpp
	symbols/TypeSymbols.cpp

	${CMAKE_CURRENT_BINARY_DIR}/AllSyntax.cpp
	syntax/SyntaxFacts.cpp
	syntax/SyntaxNode.cpp
	syntax/SyntaxPrinter.cpp
	syntax/SyntaxTree.cpp
	syntax/SyntaxVisitor.cpp

	text/SFormat.cpp
	text/SourceManager.cpp

	${CMAKE_CURRENT_BINARY_DIR}/Version.cpp
	util/BumpAllocator.cpp
	util/Hash.cpp
	util/Util.cpp
)

add_dependencies(slang gen_version)

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
		-Wchar-subscripts
		-Wcomma
		-Wconditional-uninitialized
		-Wconversion
		-Wdelete-non-virtual-dtor
		-Wdeprecated
		-Wduplicate-enum
		-Wduplicate-method-arg
		-Wembedded-directive
		-Wfor-loop-analysis
		-Wformat-pedantic
		-Widiomatic-parentheses
		-Wimplicit-fallthrough
		-Wpedantic
		-Wrange-loop-analysis
		-Wredundant-parens
		-Wreserved-id-macro
		-Wshadow
		-Wundefined-reinterpret-cast
		-Wunreachable-code-aggressive
		-Wzero-as-null-pointer-constant
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
