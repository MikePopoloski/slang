add_executable(simtests
    BitcodeTests.cpp
    JITTests.cpp
    main.cpp
)

target_link_libraries(simtests PRIVATE slang CONAN_PKG::Catch2)
target_link_libraries(simtests PRIVATE CONAN_PKG::fmt)

add_test(NAME simtests COMMAND simtests)
