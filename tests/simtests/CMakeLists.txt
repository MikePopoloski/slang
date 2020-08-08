add_executable(simtests
    BitcodeTests.cpp
    JITTests.cpp
    main.cpp
)

target_link_libraries(simtests PRIVATE slangruntime slangcodegen)

add_test(NAME simtests COMMAND simtests)
