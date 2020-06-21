add_executable(driver driver/driver.cpp)
target_link_libraries(driver PRIVATE slangcore slangparser slangcompiler slangmir)
set_target_properties(driver PROPERTIES OUTPUT_NAME "slang")

install(TARGETS driver RUNTIME DESTINATION bin)

add_executable(rewriter rewriter/rewriter.cpp)
target_link_libraries(rewriter PRIVATE slangcore slangparser slangcompiler slangmir)

if(FUZZ_TARGET)
    message("Tweaking driver for fuzz testing")
    target_compile_definitions(driver PRIVATE FUZZ_TARGET)

    target_compile_options(driver PRIVATE "-fsanitize=fuzzer")
    target_link_libraries(driver PRIVATE "-fsanitize=fuzzer")
endif()