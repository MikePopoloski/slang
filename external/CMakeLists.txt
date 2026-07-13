# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# --- fmt lib ---
if(SLANG_USE_SYSTEM_FMT)
  find_package(fmt 12.2 REQUIRED)

  get_target_property(FMT_CFG fmt::fmt IMPORTED_CONFIGURATIONS)
  list(GET FMT_CFG 0 FMT_CFG_FIRST)
  get_target_property(FMT_LIB fmt::fmt IMPORTED_LOCATION_${FMT_CFG_FIRST})
  get_target_property(FMT_INC fmt::fmt INTERFACE_INCLUDE_DIRECTORIES)
  message(STATUS "Found system fmt library: ${FMT_LIB}")
  message(STATUS "Using system fmt include: ${FMT_INC}")

  set(fmt_target "fmt::fmt")
else()
  FetchContent_Declare(
    fmt
    GIT_REPOSITORY https://github.com/fmtlib/fmt.git
    GIT_TAG 12.2.0
    GIT_SHALLOW ON
    SYSTEM EXCLUDE_FROM_ALL)
  FetchContent_MakeAvailable(fmt)

  # The fmt-header-only target unconditionally defines FMT_HEADER_ONLY, which
  # pulls the entire fmt implementation into every TU that includes a fmt
  # header. We strip that define here and instead manually build the definitions
  # into one TU (Fmt.cpp).
  set_property(TARGET fmt-header-only PROPERTY INTERFACE_COMPILE_DEFINITIONS)

  # The slang library compiles the fmt definitions into a single TU (Fmt.cpp)
  # using PIC as needed, but the compiled fmt target is still used by
  # non-exported consumers (tools, tests, bindings). Make sure it's built with
  # PIC when it may be linked into a shared library or the Python module.
  if((SLANG_INCLUDE_PYLIB OR BUILD_SHARED_LIBS) AND TARGET fmt)
    set_target_properties(fmt PROPERTIES POSITION_INDEPENDENT_CODE ON)
  endif()

  message(STATUS "Using remote fmt library (header-only)")

  # Wrap in BUILD_INTERFACE so the header-only usage requirements apply only
  # while building slang and don't leak into the installed/exported interface.
  set(fmt_target "$<BUILD_INTERFACE:fmt::fmt-header-only>")
endif()

# --- boost ---
# By default slang stays header-only and consumes a vendored boost_unordered
# header plus a FetchContent'd header-only boost::regex, avoiding a transitive
# boost dependency for downstream consumers. Set SLANG_USE_SYSTEM_BOOST to link
# against a system-installed boost instead.
if(SLANG_USE_SYSTEM_BOOST)
  find_package(Boost 1.87.0 CONFIG REQUIRED)
  message(
    STATUS "Found system boost ${Boost_VERSION_STRING} at ${Boost_INCLUDE_DIRS}"
  )
else()
  message(STATUS "Using vendored boost_unordered header")

  add_library(boost_unordered INTERFACE)
  add_library(Boost::headers ALIAS boost_unordered)

  # slang uses boost::regex (in place of std::regex) as a header-only library.
  # We fetch just the regex repo; boost.regex auto-detects standalone mode by
  # the absence of <boost/config.hpp> and falls back to the C++ standard library
  # for its dependencies. We don't add_subdirectory the fetched repo
  # (SOURCE_SUBDIR pointed at a non-existent path makes
  # FetchContent_MakeAvailable populate only).
  message(STATUS "Using FetchContent for boost::regex (header-only)")
  FetchContent_Declare(
    boost_regex
    GIT_REPOSITORY https://github.com/MikePopoloski/regex.git
    GIT_TAG boost-1.91.0
    GIT_SHALLOW ON
    SOURCE_SUBDIR _no_build_)
  FetchContent_MakeAvailable(boost_regex)

  target_include_directories(
    boost_unordered SYSTEM
    INTERFACE "$<BUILD_INTERFACE:${boost_regex_SOURCE_DIR}/include>")
endif()

# --- mimalloc ---
if(SLANG_USE_MIMALLOC)
  if(CMAKE_SYSTEM_NAME MATCHES "Windows" AND BUILD_SHARED_LIBS)
    message(
      FATAL_ERROR "mimalloc cannot be used with Windows shared lib builds")
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
    FIND_PACKAGE_ARGS 3.3)
  FetchContent_MakeAvailable(mimalloc)

  if(mimalloc_FOUND)
    if(TARGET mimalloc)
      set(mimalloc_target "mimalloc")
    elseif(TARGET mimalloc-static)
      set(mimalloc_target "mimalloc-static")
    else()
      message(FATAL_ERROR "Could not find mimalloc target")
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
      message(FATAL_ERROR "Could not find mimalloc-obj target")
    endif()
    set(mimalloc_target "$<BUILD_INTERFACE:mimalloc-obj>")
    message(STATUS "Using remote mimalloc library")
  endif()
endif()

# --- catch2 ---
if(SLANG_INCLUDE_TESTS)
  FetchContent_Declare(
    Catch2
    GIT_REPOSITORY https://github.com/catchorg/Catch2.git
    GIT_TAG v3.15.2
    GIT_SHALLOW ON
    FIND_PACKAGE_ARGS 3.15)
  FetchContent_MakeAvailable(Catch2)

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
if(SLANG_USE_SYSTEM_TOMLPLUSPLUS)
  find_package(tomlplusplus 3.4 REQUIRED)
  get_target_property(TOML_LIB tomlplusplus::tomlplusplus IMPORTED_LOCATION)
  get_target_property(TOML_INC tomlplusplus::tomlplusplus
                      INTERFACE_INCLUDE_DIRECTORIES)
  message(STATUS "Found system tomlplusplus library: ${TOML_LIB}")
  message(STATUS "Using system tomlplusplus include: ${TOML_INC}")
  set(tomlplusplus_target "tomlplusplus::tomlplusplus")
else()
  FetchContent_Declare(
    tomlplusplus
    GIT_REPOSITORY https://github.com/marzer/tomlplusplus.git
    GIT_TAG v3.4.0
    GIT_SHALLOW ON
    FIND_PACKAGE_ARGS 3.4)
  FetchContent_MakeAvailable(tomlplusplus)

  if(tomlplusplus_FOUND)
    get_target_property(TOMLPP_INC tomlplusplus::tomlplusplus
                        INTERFACE_INCLUDE_DIRECTORIES)
    message(STATUS "Found system tomlplusplus library: ${TOMLPP_INC}")
    set(tomlplusplus_target "tomlplusplus::tomlplusplus")
  else()
    message(STATUS "Using remote tomlplusplus library")
    if(IS_DIRECTORY "${tomlplusplus_SOURCE_DIR}")
      set_property(DIRECTORY ${tomlplusplus_SOURCE_DIR}
                   PROPERTY EXCLUDE_FROM_ALL YES)
    endif()
    set(tomlplusplus_target "$<BUILD_INTERFACE:tomlplusplus::tomlplusplus>")
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

  if(NOT SLANG_USE_SYSTEM_BOOST)
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

  if(SLANG_USE_THREADS)
    install(
      FILES ${PROJECT_SOURCE_DIR}/external/BS_thread_pool.hpp
      DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
      COMPONENT slang_Development)
  endif()
endif()
