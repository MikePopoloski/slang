# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# The functionality here is based on the work by Ryan Pavlik:
# https://github.com/rpavlik/cmake-modules/blob/main/GetGitRevisionDescription.cmake

if(__get_git_version)
  return()
endif()
set(__get_git_version YES)

# We must run the following at "include" time, not at function call time, to
# find the path to this module rather than the path to a calling list file
get_filename_component(_gitversionmoddir ${CMAKE_CURRENT_LIST_FILE} PATH)

# Update variables set in _refspecvar and _hashvar to the current git HEAD's ref and hash
# If we are not operating in a standard repo, worktree, or sub-module these will be set to:
#   'GITDIR-NOTFOUND'. This allows the upstream CMake to opt not to use this functionality.
function(get_git_head_revision _refspecvar _hashvar)
  # Start by checking we are operating in a git setup for slang
  # This is equivalent to the previous check that the GIT_DIR begin relative to CMAKE_SOURCE_DIR
  execute_process(
      COMMAND "${GIT_EXECUTABLE}" rev-parse --show-toplevel
      WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
      OUTPUT_VARIABLE _git_toplevel RESULT_VARIABLE _result
      ERROR_QUIET OUTPUT_STRIP_TRAILING_WHITESPACE)

  # We are not in a git project
  if (NOT _result EQUAL 0)
    set(${_refspecvar}
        "GITDIR-NOTFOUND"
        PARENT_SCOPE)
    set(${_hashvar}
        "GITDIR-NOTFOUND"
        PARENT_SCOPE)
    return()
  endif()

  # If we are in a vendored project
  # Must be done after the return-value check to avoid RELATIVE_PATH erroring 
  #   out when there is no _git_toplevel
  file(RELATIVE_PATH _relative_to_source_dir "${CMAKE_SOURCE_DIR}"
       "${_git_toplevel}")
  if ("${_relative_to_source_dir}" MATCHES "[.][.]")
    set(${_refspecvar}
        "GITDIR-NOTFOUND"
        PARENT_SCOPE)
    set(${_hashvar}
        "GITDIR-NOTFOUND"
        PARENT_SCOPE)
    return()
  endif()

  # Directly use git rev-parse to get the head file for the current branch
  # Works in plain repos, worktrees, and submodules
  execute_process(
      COMMAND "${GIT_EXECUTABLE}" rev-parse --git-path HEAD
      WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
      OUTPUT_VARIABLE HEAD_SOURCE_FILE RESULT_VARIABLE _result
      ERROR_QUIET OUTPUT_STRIP_TRAILING_WHITESPACE)

  # Check the command found a valid HEAD file
  if (NOT _result EQUAL 0 OR NOT EXISTS "${HEAD_SOURCE_FILE}")
    set(${_refspecvar}
        "GITDIR-NOTFOUND"
        PARENT_SCOPE)
    set(${_hashvar}
        "GITDIR-NOTFOUND"
        PARENT_SCOPE)
    return()
  endif()

  # Now find the GIT_DIR using rev-parse
  execute_process(
      COMMAND "${GIT_EXECUTABLE}" rev-parse --git-common-dir
      WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
      OUTPUT_VARIABLE GIT_DIR RESULT_VARIABLE _result
      ERROR_QUIET OUTPUT_STRIP_TRAILING_WHITESPACE)

  if(NOT _result EQUAL 0 OR "${GIT_DIR}" STREQUAL "")
    set(${_refspecvar}
        "GITDIR-NOTFOUND"
        PARENT_SCOPE)
    set(${_hashvar}
        "GITDIR-NOTFOUND"
        PARENT_SCOPE)
    return()
  endif()

  # Absolutize the GIT_DIR and HEAD_SOURCE_FILE
  get_filename_component(GIT_DIR "${GIT_DIR}" ABSOLUTE
                         BASE_DIR "${CMAKE_CURRENT_SOURCE_DIR}")
  get_filename_component(HEAD_SOURCE_FILE "${HEAD_SOURCE_FILE}" ABSOLUTE
                         BASE_DIR "${CMAKE_CURRENT_SOURCE_DIR}")

  set(GIT_DATA "${CMAKE_CURRENT_BINARY_DIR}/CMakeFiles/git-data")
  if(NOT EXISTS "${GIT_DATA}")
    file(MAKE_DIRECTORY "${GIT_DATA}")
  endif()

  set(HEAD_FILE "${GIT_DATA}/HEAD")
  configure_file("${HEAD_SOURCE_FILE}" "${HEAD_FILE}" COPYONLY)

  configure_file("${_gitversionmoddir}/gitversion.cmake.in"
                 "${GIT_DATA}/grabRef.cmake" @ONLY)
  include("${GIT_DATA}/grabRef.cmake")

  set(${_refspecvar}
      "${HEAD_REF}"
      PARENT_SCOPE)
  set(${_hashvar}
      "${HEAD_HASH}"
      PARENT_SCOPE)
endfunction()

function(get_git_version _patch _prerelease _hash)
  if(NOT GIT_FOUND)
    find_package(Git QUIET)
  endif()
  get_git_head_revision(refspec hash)

  set(${_patch}
      0
      PARENT_SCOPE)
  set(${_prerelease}
      ""
      PARENT_SCOPE)
  set(${_hash}
      0
      PARENT_SCOPE)

  if(NOT GIT_FOUND OR NOT hash)
    return()
  endif()

  execute_process(
    COMMAND ${GIT_EXECUTABLE} describe --tags --dirty
    WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
    OUTPUT_VARIABLE _version_string
    ERROR_QUIET OUTPUT_STRIP_TRAILING_WHITESPACE)

  set(local_prerelease "")
  if(${_version_string} MATCHES ".+-([0-9]+-g[0-9a-z]+).*")
    # The tag may include a prerelease suffix (e.g. v11.0rc1), so capture any
    # non-dash characters between the major.minor version and the commit count
    # produced by `git describe` as the prerelease segment.
    string(REGEX REPLACE "^v?[0-9]+\\.[0-9]+([^-]*)-[0-9]+-g[0-9a-z]+.*" "\\1"
                         local_prerelease "${_version_string}")
    string(REGEX REPLACE "^v?[0-9]+\\.[0-9]+[^-]*-([0-9]+)-g[0-9a-z]+.*" "\\1"
                         local_patch "${_version_string}")
    string(REGEX REPLACE "^v?[0-9]+\\.[0-9]+[^-]*-[0-9]+-g([0-9a-z]+).*" "\\1"
                         local_hash "${_version_string}")
  else()
    set(local_patch 0)
    # No additional commits since the tag; extract a prerelease suffix directly
    # from the tag itself if present (e.g. v11.0rc1 or v11.0rc1-dirty).
    if(${_version_string} MATCHES "^v?[0-9]+\\.[0-9]+([^-]+)")
      set(local_prerelease "${CMAKE_MATCH_1}")
    endif()
    execute_process(
      COMMAND ${GIT_EXECUTABLE} rev-parse --short HEAD
      WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
      OUTPUT_VARIABLE local_hash
      ERROR_QUIET OUTPUT_STRIP_TRAILING_WHITESPACE)
  endif()

  set(${_patch}
      ${local_patch}
      PARENT_SCOPE)
  set(${_prerelease}
      ${local_prerelease}
      PARENT_SCOPE)
  set(${_hash}
      ${local_hash}
      PARENT_SCOPE)
endfunction()
