# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# Required minimum versions for dependencies
set(fmt_min_version "12.1")
set(mimalloc_min_version "3.3")
set(cpptrace_min_version "1.0")
set(catch2_min_version "3.14")
set(tomlplusplus_min_version "3.4")

# --- fmt lib ---
set(find_pkg_args "")
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
  set(find_pkg_args "FIND_PACKAGE_ARGS" "${fmt_min_version}")
endif()

set(FMT_SYSTEM_HEADERS
    ON
    CACHE INTERNAL "")

FetchContent_Declare(
  fmt
  GIT_REPOSITORY https://github.com/fmtlib/fmt.git
  GIT_TAG 12.1.0
  GIT_SHALLOW ON
  ${find_pkg_args})

# Force fmtlib to always be a static lib if we pull it via FetchContent (i.e.
# not intercepted by find_package), since it's a private dependency that's
# mostly header-only already.
set(saved_build_shared_libs ${BUILD_SHARED_LIBS})
set(BUILD_SHARED_LIBS OFF)
FetchContent_MakeAvailable(fmt)
set(BUILD_SHARED_LIBS ${saved_build_shared_libs})

if(NOT TARGET fmt::fmt)
  message(
    FATAL_ERROR "Could not find fmt package, min version: ${fmt_min_version}")
endif()

if((SLANG_INCLUDE_PYLIB OR BUILD_SHARED_LIBS) AND NOT fmt_FOUND)
  set_target_properties(fmt PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()

if(fmt_FOUND)
  get_target_property(FMT_CFG fmt::fmt IMPORTED_CONFIGURATIONS)
  list(GET FMT_CFG 0 FMT_CFG_FIRST)
  get_target_property(FMT_LIB fmt::fmt IMPORTED_LOCATION_${FMT_CFG_FIRST})
  get_target_property(FMT_INC fmt::fmt INTERFACE_INCLUDE_DIRECTORIES)
  message(STATUS "Found system fmt library: ${FMT_LIB}")
  message(STATUS "Using system fmt include: ${FMT_INC}")
else()
  message(STATUS "Using remote fmt library")
endif()

# --- boost ---
find_package(Boost 1.87.0 CONFIG QUIET)
if(NOT Boost_FOUND)
  message(STATUS "Using vendored boost_unordered header")

  add_library(boost_unordered INTERFACE)
  add_library(Boost::headers ALIAS boost_unordered)
  target_compile_definitions(boost_unordered
                             INTERFACE SLANG_BOOST_SINGLE_HEADER)
else()
  message(
    STATUS "Found system boost ${Boost_VERSION_STRING} at ${Boost_INCLUDE_DIRS}"
  )
endif()

# --- mimalloc ---
if(SLANG_USE_MIMALLOC)
  if(CMAKE_SYSTEM_NAME MATCHES "Windows" AND BUILD_SHARED_LIBS)
    message(
      FATAL_ERROR "mimalloc cannot be used with Windows shared lib builds")
  endif()

  set(find_pkg_args "")
  if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
    set(find_pkg_args "FIND_PACKAGE_ARGS")
  endif()

  set(MI_BUILD_SHARED
      OFF
      CACHE INTERNAL "")
  set(MI_BUILD_STATIC
      OFF
      CACHE INTERNAL "")
  set(MI_BUILD_TESTS
      OFF
      CACHE INTERNAL "")
  set(MI_SKIP_COLLECT_ON_EXIT
      ON
      CACHE INTERNAL "")
  set(MI_USE_CXX
      ON
      CACHE INTERNAL "")

  FetchContent_Declare(
    mimalloc
    GIT_REPOSITORY https://github.com/microsoft/mimalloc.git
    GIT_TAG v3.3.2
    GIT_SHALLOW ON
    ${find_pkg_args})
  FetchContent_MakeAvailable(mimalloc)

  if(mimalloc_FOUND)
    if(TARGET mimalloc)
      set(mimalloc_target "mimalloc")
    elseif(TARGET mimalloc-static)
      set(mimalloc_target "mimalloc-static")
    else()
      message(
        FATAL_ERROR
          "Could not find mimalloc package, min version: ${mimalloc_min_version}"
      )
    endif()

    get_target_property(MIMALLOC_CFG ${mimalloc_target} IMPORTED_CONFIGURATIONS)
    list(GET MIMALLOC_CFG 0 MIMALLOC_CFG_FIRST)
    get_target_property(MIMALLOC_LIB ${mimalloc_target}
                        IMPORTED_LOCATION_${MIMALLOC_CFG_FIRST})
    get_target_property(MIMALLOC_INC ${mimalloc_target}
                        INTERFACE_INCLUDE_DIRECTORIES)
    message(STATUS "Found system mimalloc library: ${MIMALLOC_LIB}")
    message(STATUS "Using system mimalloc include: ${MIMALLOC_INC}")
  else()
    if(NOT TARGET mimalloc-obj)
      message(
        FATAL_ERROR
          "Could not find mimalloc package, min version: ${mimalloc_min_version}"
      )
    endif()
    set(mimalloc_target "$<BUILD_INTERFACE:mimalloc-obj>")
    message(STATUS "Using remote mimalloc library")
  endif()
endif()

# --- cpptrace ---
if(SLANG_USE_CPPTRACE)
  set(find_pkg_args "")
  if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
    set(find_pkg_args "FIND_PACKAGE_ARGS" "${cpptrace_min_version}")
  endif()

  set(CPPTRACE_BUILD_SHARED
      OFF
      CACHE INTERNAL "")

  FetchContent_Declare(
    cpptrace
    GIT_REPOSITORY https://github.com/jeremy-rifkin/cpptrace.git
    GIT_TAG v1.0.4
    GIT_SHALLOW ON
    ${find_pkg_args})
  FetchContent_MakeAvailable(cpptrace)

  if(cpptrace_FOUND)
    get_target_property(CPPTRACE_INC cpptrace INTERFACE_INCLUDE_DIRECTORIES)
    message(STATUS "Found system cpptrace library: ${CPPTRACE_INC}")
  else()
    message(STATUS "Using remote cpptrace library")
    if(IS_DIRECTORY "${cpptrace_SOURCE_DIR}")
      set_property(DIRECTORY ${cpptrace_SOURCE_DIR} PROPERTY EXCLUDE_FROM_ALL
                                                             YES)
    endif()
  endif()
endif()

# --- catch2 ---
if(SLANG_INCLUDE_TESTS)
  set(find_pkg_args "")
  if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
    set(find_pkg_args "FIND_PACKAGE_ARGS" "${catch2_min_version}")
  endif()

  FetchContent_Declare(
    Catch2
    GIT_REPOSITORY https://github.com/catchorg/Catch2.git
    GIT_TAG v3.14.0
    GIT_SHALLOW ON
    ${find_pkg_args})
  FetchContent_MakeAvailable(Catch2)

  if(NOT TARGET Catch2::Catch2)
    message(
      FATAL_ERROR
        "Could not find Catch2 package, min version: ${catch2_min_version}")
  endif()

  if(Catch2_FOUND)
    get_target_property(Catch2_INCLUDE_DIR Catch2::Catch2
                        INTERFACE_INCLUDE_DIRECTORIES)
    message(STATUS "Found system Catch2 version: ${Catch2_VERSION}")
    message(STATUS "Using system Catch2 include: ${Catch2_INCLUDE_DIR}")
  else()
    message(STATUS "Using remote Catch2 library")
  endif()
endif()

# --- tomlplusplus ---
# Always FetchContent rather than opportunistically picking up a system pkg:
# distro tomlplusplus is typically built as a shared lib with TOML_HEADER_ONLY=0
# and TOML_SHARED_LIB=1 baked into its imported target, which clashes with the
# per-TU TOML_EXCEPTIONS=0 override that WaiverManager.cpp relies on. Fetching
# the upstream subdir gives a header-only INTERFACE target everywhere.
FetchContent_Declare(
  tomlplusplus
  GIT_REPOSITORY https://github.com/marzer/tomlplusplus.git
  GIT_TAG v3.4.0
  GIT_SHALLOW ON)
FetchContent_MakeAvailable(tomlplusplus)

if(NOT TARGET tomlplusplus::tomlplusplus)
  message(
    FATAL_ERROR
      "Could not find tomlplusplus package, min version: ${tomlplusplus_min_version}"
  )
endif()

if(tomlplusplus_FOUND)
  get_target_property(TOMLPP_INC tomlplusplus::tomlplusplus
                      INTERFACE_INCLUDE_DIRECTORIES)
  message(STATUS "Found system tomlplusplus library: ${TOMLPP_INC}")
else()
  message(STATUS "Using remote tomlplusplus library")
  if(IS_DIRECTORY "${tomlplusplus_SOURCE_DIR}")
    set_property(DIRECTORY ${tomlplusplus_SOURCE_DIR} PROPERTY EXCLUDE_FROM_ALL
                                                               YES)
  endif()
endif()

# --- install rules ---
if(SLANG_INCLUDE_INSTALL)
  install(
    DIRECTORY ${PROJECT_SOURCE_DIR}/external/ieee1800/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/ieee1800
    COMPONENT slang_Development)
  install(
    FILES ${PROJECT_SOURCE_DIR}/external/expected.hpp
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
    COMPONENT slang_Development)

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

  if(NOT Boost_FOUND)
    install(
      TARGETS boost_unordered
      EXPORT slangTargets
      COMPONENT slang_Development)
    install(
      FILES ${PROJECT_SOURCE_DIR}/external/boost_unordered.hpp
            ${PROJECT_SOURCE_DIR}/external/boost_concurrent.hpp
      DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
      COMPONENT slang_Development)
  endif()

  if(SLANG_USE_CPPTRACE AND NOT cpptrace_FOUND)
    install(
      TARGETS cpptrace-lib
      EXPORT slangTargets
      COMPONENT slang_Development)
  endif()

  if(SLANG_USE_THREADS)
    install(
      FILES ${PROJECT_SOURCE_DIR}/external/BS_thread_pool.hpp
      DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
      COMPONENT slang_Development)
  endif()

  if(NOT tomlplusplus_FOUND)
    install(
      TARGETS tomlplusplus_tomlplusplus
      EXPORT slangTargets
      COMPONENT slang_Development)
    install(
      DIRECTORY ${tomlplusplus_SOURCE_DIR}/include/toml++
      DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
      COMPONENT slang_Development)
  endif()
endif()
