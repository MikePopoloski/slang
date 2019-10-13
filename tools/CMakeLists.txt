add_executable(driver driver/driver.cpp)
target_link_libraries(driver PRIVATE slang)

add_executable(rewriter rewriter/rewriter.cpp)
target_link_libraries(rewriter PRIVATE slang)

if(FUZZ_TARGET)
	message("Tweaking driver for fuzz testing")
	target_compile_definitions(driver PRIVATE FUZZ_TARGET)
endif()