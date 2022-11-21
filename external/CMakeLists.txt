# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

set(find_pkg_args "")
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
  set(find_pkg_args "FIND_PACKAGE_ARGS" "9.0.0")
endif()

FetchContent_Declare(
  fmt
  GIT_REPOSITORY https://github.com/fmtlib/fmt.git
  GIT_TAG 9.1.0
  GIT_SHALLOW ON
  ${find_pkg_args})

# Force fmtlib to always be a static lib if we pull it via FetchContent (i.e.
# not intercepted by find_package), since it's a private dependency that's
# mostly header-only already.
set(saved_build_shared_libs ${BUILD_SHARED_LIBS})
set(BUILD_SHARED_LIBS OFF)
FetchContent_MakeAvailable(fmt)
set(BUILD_SHARED_LIBS ${saved_build_shared_libs})

if((SLANG_INCLUDE_PYLIB OR BUILD_SHARED_LIBS) AND NOT fmt_FOUND)
  set_target_properties(fmt PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()

if(fmt_FOUND)
  get_target_property(FMT_CFG fmt::fmt IMPORTED_CONFIGURATIONS)
  get_target_property(FMT_LIB fmt::fmt IMPORTED_LOCATION_${FMT_CFG})
  get_target_property(FMT_INC fmt::fmt INTERFACE_INCLUDE_DIRECTORIES)
  message(STATUS "Found system fmt library: ${FMT_LIB}")
  message(STATUS "Using system fmt include: ${FMT_INC}")
else()
  message(STATUS "Using remote fmt library")
endif()

set(find_pkg_args "")
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
  set(find_pkg_args "FIND_PACKAGE_ARGS" "2.0.1")
endif()

FetchContent_Declare(
  unordered_dense
  GIT_REPOSITORY https://github.com/martinus/unordered_dense.git
  GIT_TAG v2.0.0
  GIT_SHALLOW ON
  ${find_pkg_args})
FetchContent_MakeAvailable(unordered_dense)

if(SLANG_INCLUDE_INSTALL)
  install(
    DIRECTORY ${PROJECT_SOURCE_DIR}/external/ieee1800/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/ieee1800
    COMPONENT slang_Development)
  install(
    FILES ${PROJECT_SOURCE_DIR}/external/flat_hash_map.hpp
          ${PROJECT_SOURCE_DIR}/external/span.hpp
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
    COMPONENT slang_Development)
  if(NOT unordered_dense_FOUND)
    install(
      DIRECTORY ${unordered_dense_SOURCE_DIR}/include/ankerl
      DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
      COMPONENT slang_Development)
  endif()

  if(NOT fmt_FOUND)
    install(
      TARGETS fmt
      EXPORT slangTargets
      LIBRARY COMPONENT slang_Development
      ARCHIVE COMPONENT slang_Development
      PUBLIC_HEADER EXCLUDE_FROM_ALL
      PRIVATE_HEADER EXCLUDE_FROM_ALL)
    install(
      DIRECTORY ${fmt_SOURCE_DIR}/include/fmt
      DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
      COMPONENT slang_Development)
  endif()

  if(NOT unordered_dense_FOUND)
    install(TARGETS unordered_dense EXPORT slangTargets)
  endif()
endif()
