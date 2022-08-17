add_executable(simtests BitcodeTests.cpp JITTests.cpp)

target_link_libraries(simtests PRIVATE slangruntime slangcodegen Catch2::Catch2WithMain)

add_test(NAME simtests COMMAND simtests)
set_tests_properties(simtests PROPERTIES TIMEOUT 60)
