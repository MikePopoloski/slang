add_executable(depmap depmap/depmap.cpp)
target_link_libraries(depmap PRIVATE slang)

add_executable(driver driver/driver.cpp)
target_link_libraries(driver PRIVATE slang CONAN_PKG::CLI11)

add_executable(rewriter rewriter/rewriter.cpp)
target_link_libraries(rewriter PRIVATE slang)
