add_executable(simtests
    BitcodeTests.cpp
    JITTests.cpp
    main.cpp
)

target_link_libraries(simtests PRIVATE slangcore slangparser slangcompiler slangmir slangruntime slangcodegen CONAN_PKG::catch2)

add_test(NAME simtests COMMAND simtests)
