add_executable(
  tidy_unittests
  ../../../tests/unittests/main.cpp ../../../tests/unittests/Test.cpp
  OnlyAssignedOnResetTest.cpp RegisterHasNoResetTest.cpp)

target_link_libraries(
  tidy_unittests
  PRIVATE slang::slang Catch2::Catch2 fmt::fmt
  PUBLIC ${SLANG_LIBRARIES})
target_compile_definitions(tidy_unittests PRIVATE UNITTESTS)
target_include_directories(tidy_unittests PRIVATE ../include ../../../include
                                                  ../../../tests/unittests)

if(CI_BUILD)
  message("Running CI build")
  target_compile_definitions(tidy_unittests PRIVATE CI_BUILD)
endif()

add_test(NAME tidy_unittests COMMAND tidy_unittests)
