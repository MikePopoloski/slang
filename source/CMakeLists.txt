add_library(slang STATIC
	binding/ConstantValue.cpp
	binding/EvalContext.cpp
	binding/Expressions.cpp
	binding/Expressions_eval.cpp
	binding/Expressions_prop.cpp
	binding/Statements.cpp

	compilation/BuiltInSubroutines.cpp
	compilation/Compilation.cpp

	diagnostics/Diagnostics.cpp

	lexing/Lexer.cpp
	lexing/LexerFacts.cpp
	lexing/Preprocessor.cpp
	lexing/Token.cpp

	numeric/SVInt.cpp
	numeric/Time.cpp
	numeric/VectorBuilder.cpp

	parsing/AllSyntax.cpp
	parsing/Parser.cpp
	parsing/Parser_expressions.cpp
	parsing/Parser_statements.cpp
	parsing/ParserBase.cpp
	parsing/SyntaxFacts.cpp
	parsing/SyntaxNode.cpp

	symbols/HierarchySymbols.cpp
	symbols/Lazy.cpp
	symbols/MemberSymbols.cpp
	symbols/Scope.cpp
	symbols/SemanticFacts.cpp
	symbols/StatementBodiedScope.cpp
	symbols/Symbol.cpp
	symbols/TypePrinter.cpp
	symbols/TypeSymbols.cpp

	text/SourceManager.cpp

	util/BumpAllocator.cpp
	util/Hash.cpp
	util/Util.cpp

	../external/fmt/format.cc
	../external/fmt/posix.cc
)

if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
	# Warnings as errors
	target_compile_options(slang PRIVATE /WX)
else()
	# Link against C++17 filesystem
	target_link_libraries(slang PUBLIC stdc++fs)
endif()

target_include_directories(slang PUBLIC ./)
target_include_directories(slang PUBLIC ../external/)