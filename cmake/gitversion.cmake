# Execute git describe to get our version number.
set(SLANG_VERSION_MAJOR 0)
set(SLANG_VERSION_MINOR 0)
set(SLANG_VERSION_PATCH 0)
set(SLANG_VERSION_HASH 0)
set(SLANG_VERSION_STRING 0.0.0)

find_package(Git)
if(GIT_FOUND)
  execute_process(
    COMMAND ${GIT_EXECUTABLE} describe --tags --dirty --always
    WORKING_DIRECTORY "${local_dir}"
    OUTPUT_VARIABLE _version_string
    ERROR_QUIET OUTPUT_STRIP_TRAILING_WHITESPACE)

  string(REGEX REPLACE "^v?([0-9]+).*" "\\1" SLANG_VERSION_MAJOR
                       "${_version_string}")
  string(REGEX REPLACE "^v?[0-9]+\\.([0-9]+).*" "\\1" SLANG_VERSION_MINOR
                       "${_version_string}")

  if(${_version_string} MATCHES ".+-([0-9]+-g[0-9a-z]+).*")
    string(REGEX REPLACE "^v?[0-9]+\\.[0-9]+-([0-9]+).*" "\\1"
                         SLANG_VERSION_PATCH "${_version_string}")
    string(REGEX REPLACE "^v?[0-9]+\\.[0-9]+-[0-9]+-g([0-9a-z]+).*" "\\1"
                         SLANG_VERSION_HASH "${_version_string}")
  else()
    execute_process(
      COMMAND ${GIT_EXECUTABLE} rev-parse --short HEAD
      WORKING_DIRECTORY "${local_dir}"
      OUTPUT_VARIABLE SLANG_VERSION_HASH
      ERROR_QUIET OUTPUT_STRIP_TRAILING_WHITESPACE)
  endif()
  set(SLANG_VERSION_STRING
      ${SLANG_VERSION_MAJOR}.${SLANG_VERSION_MINOR}.${SLANG_VERSION_PATCH})

  message(
    STATUS "slang version is ${SLANG_VERSION_STRING}+${SLANG_VERSION_HASH}")
else()
  message(STATUS "git not found, no version set")
endif()

configure_file(${infile} ${outfile} @ONLY)
