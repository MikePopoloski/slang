# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

install(
  TARGETS slang_slang
  EXPORT slangTargets
  RUNTIME COMPONENT slang_Runtime
  LIBRARY COMPONENT slang_Runtime NAMELINK_COMPONENT slang_Development
  ARCHIVE COMPONENT slang_Development
  INCLUDES
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

if(SLANG_INCLUDE_TOOLS)
  install(TARGETS slang_driver RUNTIME COMPONENT slang_Runtime)
endif()

include(CMakePackageConfigHelpers)

# Package export / installation rules
set(SLANG_CMAKECONFIG_INSTALL_DIR
    "${CMAKE_INSTALL_LIBDIR}/cmake/${PROJECT_NAME}"
    CACHE STRING "install path for slangConfig.cmake")

install(
  EXPORT slangTargets
  NAMESPACE "slang::"
  DESTINATION ${SLANG_CMAKECONFIG_INSTALL_DIR}
  COMPONENT slang_Development)

if(fmt_FOUND)
  set(FMT_FIND_DEP "find_dependency(fmt)")
endif()
if(Boost_FOUND)
  set(BOOST_FIND_DEP "find_dependency(Boost)")
endif()
if(mimalloc_FOUND)
  set(MIMALLOC_FIND_DEP "find_dependency(mimalloc)")
endif()

configure_package_config_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/cmake/slangConfig.cmake.in
  "${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}Config.cmake"
  INSTALL_DESTINATION ${SLANG_CMAKECONFIG_INSTALL_DIR})

write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}ConfigVersion.cmake
  VERSION ${PROJECT_VERSION}
  COMPATIBILITY SameMajorVersion)

install(
  FILES ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}Config.cmake
        ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}ConfigVersion.cmake
  DESTINATION ${SLANG_CMAKECONFIG_INSTALL_DIR}
  COMPONENT slang_Development)

if(UNIX)
  # Install pkg-config input file
  configure_file(${CMAKE_CURRENT_SOURCE_DIR}/scripts/sv-lang.pc.in
                 ${CMAKE_CURRENT_BINARY_DIR}/sv-lang.pc @ONLY)
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/sv-lang.pc
          DESTINATION ${CMAKE_INSTALL_DATAROOTDIR}/pkgconfig)
endif()
