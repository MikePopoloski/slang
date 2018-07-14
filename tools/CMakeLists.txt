add_executable(depmap depmap/main.cpp)
target_link_libraries(depmap PRIVATE slang)

add_executable(driver driver/main.cpp)
target_link_libraries(driver PRIVATE slang)
