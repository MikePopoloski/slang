add_executable(unittests
	DiagnosticTests.cpp
	EvalTests.cpp
	ExpressionParsingTests.cpp
	ExpressionTests.cpp
	FileTests.cpp
	HierarchyTests.cpp
	LexerTests.cpp
	main.cpp
	MemberParsingTests.cpp
	MemberTests.cpp
	NumericTests.cpp
	PreprocessorTests.cpp
	RewriterTests.cpp
	StatementParsingTests.cpp
	SymbolLookupTests.cpp
	TypeTests.cpp
)

target_link_libraries(unittests PRIVATE slang CONAN_PKG::catch2)

# Copy the data directory for running tests from the build folder.
add_custom_command(
	TARGET unittests POST_BUILD
	COMMAND ${CMAKE_COMMAND} -E copy_directory ${CMAKE_CURRENT_SOURCE_DIR}/data ${CMAKE_CURRENT_BINARY_DIR}/data
)

add_test(NAME unittests COMMAND unittests)
