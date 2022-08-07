add_executable(driver driver/driver.cpp)
target_link_libraries(driver PRIVATE slangcompiler)
if(STATIC_BUILD)
  target_link_libraries(driver PRIVATE -static -Wl,--whole-archive -lpthread
                                       -Wl,--no-whole-archive)
endif()
set_target_properties(driver PROPERTIES OUTPUT_NAME "slang")

add_executable(rewriter rewriter/rewriter.cpp)
target_link_libraries(rewriter PRIVATE slangcompiler)
if(STATIC_BUILD)
  target_link_libraries(rewriter PRIVATE -static -Wl,--whole-archive -lpthread
                                         -Wl,--no-whole-archive)
endif()

if(SLANG_INCLUDE_LLVM)
  target_compile_definitions(driver PRIVATE INCLUDE_SIM)
  target_link_libraries(driver PRIVATE slangcodegen slangruntime)
endif()

if(FUZZ_TARGET)
  message("Tweaking driver for fuzz testing")
  target_compile_definitions(driver PRIVATE FUZZ_TARGET)

  target_compile_options(driver PRIVATE "-fsanitize=fuzzer")
  target_link_libraries(driver PRIVATE "-fsanitize=fuzzer")
endif()

if(SLANG_INCLUDE_INSTALL)
  install(TARGETS driver RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()
