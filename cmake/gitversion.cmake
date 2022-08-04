set(_build_version "unknown")

find_package(Git)
if(GIT_FOUND)
 	execute_process(
    	COMMAND ${GIT_EXECUTABLE} rev-parse --short HEAD
    	WORKING_DIRECTORY "${local_dir}"
    	OUTPUT_VARIABLE _build_version
    	ERROR_QUIET
    	OUTPUT_STRIP_TRAILING_WHITESPACE
  	)
  	message(STATUS "git hash: ${_build_version}")
else()
  	message(STATUS "git not found")
endif()

configure_file(${infile} ${outfile} @ONLY)
