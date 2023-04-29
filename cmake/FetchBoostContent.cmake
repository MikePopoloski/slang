# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# The functionality here is based on the work by Alan Defreitas:
# https://github.com/alandefreitas/FetchBoostContent/blob/develop/cmake/FetchBoostContent.cmake

include_guard()
include(FetchContent)

function(__FetchBoostContent_sanitize_name name output)
  string(TOLOWER ${name} name)
  string(REPLACE "/" "_" name ${name})
  string(FIND ${name} boost_ idx)
  if(NOT idx EQUAL 0)
    message(FATAL_ERROR "Module ${name} does not have the \"boost_\" prefix")
  endif()
  set(${output}
      ${name}
      PARENT_SCOPE)
endfunction()

# A version of FetchContent_Declare for Boost Libraries This function will store
# the information about the library as a separate global property, so we can
# later identify that this is a Boost library and we need to scan its
# dependencies
function(FetchBoostContent_Declare name)
  __fetchboostcontent_sanitize_name(${name} name)

  # Check if already defined
  set(savedDetailsPropertyName "_FetchBoostContent_${name}_savedDetails")
  get_property(
    alreadyDefined GLOBAL
    PROPERTY ${savedDetailsPropertyName}
    DEFINED)
  if(alreadyDefined)
    return()
  endif()

  # Remember the package arguments
  define_property(
    GLOBAL
    PROPERTY ${savedDetailsPropertyName}
    BRIEF_DOCS "Arguments for ${name}"
    FULL_DOCS "Arguments for ${name}")
  set_property(GLOBAL PROPERTY ${savedDetailsPropertyName} ${ARGN})

  # Make an internal call to FetchContent and store it there too
  FetchContent_Declare(${name} ${ARGN})
endfunction()

# Get the library properties. This is usually used to identify if the library
# has already been populated. Variables for all other properties will still be
# set. These properties are only defined if a previous call to Populate has been
# made.
function(FetchBoostContent_GetProperties name)
  __fetchboostcontent_sanitize_name(${name} name)
  set(singleValueArgs SOURCE_DIR BINARY_DIR POPULATED)
  cmake_parse_arguments(ARG "" "${singleValueArgs}" "" ${ARGN})

  # Provide all properties if no specific properties requested
  if(NOT ARG_SOURCE_DIR
     AND NOT ARG_BINARY_DIR
     AND NOT ARG_POPULATED)
    set(ARG_SOURCE_DIR ${${name}_SOURCE_DIR})
    set(ARG_BINARY_DIR ${${name}_BINARY_DIR})
    set(ARG_POPULATED ${${name}_POPULATED})
  endif()

  # Return properties
  set(PROPERTY_SUFFIXES # Output Property / Global Property Suffix
      SOURCE_DIR sourceDir BINARY_DIR binaryDir POPULATED populated)
  while(PROPERTY_SUFFIXES)
    list(POP_FRONT PROPERTY_SUFFIXES PROPERTY SUFFIX)
    if(ARG_${PROPERTY})
      set(propertyName "_FetchBoostContent_${name}_${SUFFIX}")
      get_property(value GLOBAL PROPERTY ${propertyName})
      if(value)
        set(${ARG_${PROPERTY}}
            ${value}
            PARENT_SCOPE)
      endif()
    endif()
  endwhile()
endfunction()

# Populate the library properties from the declared data.
function(FetchBoostContent_Populate name)
  if(NOT name)
    message(
      FATAL_ERROR
        "Empty contentName not allowed for FetchBoostContent_Populate()")
  endif()
  __fetchboostcontent_sanitize_name(${name} name)

  # Call underlying Populate function This might have already been called
  # indirectly by FetchBoostContent_Populate. In this case, we just need to
  # obtain the properties and mark it as Populated directly by
  # FetchBoostContent_Populate too.
  FetchContent_GetProperties(${name})
  if(NOT ${name}_POPULATED)
    FetchContent_Populate(${name} ${ARGN})
  endif()

  # Set properties and return values based on FetchContent_Populate
  set(PROPERTY_SUFFIXES SOURCE_DIR sourceDir BINARY_DIR binaryDir POPULATED
                        populated)
  while(PROPERTY_SUFFIXES)
    list(POP_FRONT PROPERTY_SUFFIXES PROPERTY SUFFIX)
    # If FetchContent_Populate returned this property Set the boost version of
    # the property too
    if(${name}_${PROPERTY})
      set(propertyName "_FetchBoostContent_${name}_${SUFFIX}")
      define_property(
        GLOBAL
        PROPERTY ${propertyName}
        BRIEF_DOCS "POPULATED property for ${contentName}"
        FULL_DOCS "POPULATED property for ${contentName}")
      set_property(GLOBAL PROPERTY ${propertyName} ${${name}_${PROPERTY}})
      # Return the value
      set(${name}_${PROPERTY}
          ${${name}_${PROPERTY}}
          PARENT_SCOPE)
    endif()
  endwhile()

  # At this point, FetchContent would be done. If the Boost libraries have
  # already been found at the parent scope, then this is also done. This should
  # only be the case for Boost library proposals.
  if(Boost_FOUND)
    return()
  endif()

  # For Boost libraries in general, we still need to identify and populate
  # dependencies. The following replicates a logic similar to depinst.py for
  # fetching dependencies.

  # Set default options
  set(PopulateOptions
      # Option / Variable / Default
      # "enable verbose output"
      FETCH_BOOST_CONTENT_VERBOSE
      verbose
      0
      # "quiet output (opposite of -v)"
      FETCH_BOOST_CONTENT_QUIET
      quiet
      OFF
      # "exclude a default subdirectory (\"include\", \"src\", or \"test\") from
      # scan; can be repeated"
      FETCH_BOOST_CONTENT_EXCLUDE
      exclude
      ""
      # "exclude top-level dependency even when found in scan; can be repeated"
      FETCH_BOOST_CONTENT_IGNORE
      ignore
      ""
      # "additional subdirectory to scan; can be repeated"
      FETCH_BOOST_CONTENT_INCLUDE
      include
      ""
      # "ignore cache"
      FETCH_BOOST_CONTENT_IGNORE_CACHE
      ignore_cache
      0
      # "prune transitive dependencies"
      FETCH_BOOST_CONTENT_PRUNE_DEPENDENCIES
      prune_dependencies
      OFF)
  while(PopulateOptions)
    list(POP_FRONT PopulateOptions Option Variable Default)
    if(${Option})
      set(${Variable} ${${Option}})
    else()
      set(${Variable} ${Default})
    endif()
  endwhile()
  if(quiet)
    set(verbose -1)
  endif()
  set(library ${name})

  # Print according to verbose level
  function(vprint level)
    if(quiet)
      return()
    endif()
    if(verbose GREATER_EQUAL level)
      # Verbosity level will come from CMake, while this allows a lower custom
      # level
      if(level GREATER_EQUAL 2)
        message("${ARGN}")
      elseif(level EQUAL 1 OR verbose EQUAL 0)
        message(STATUS "${ARGN}")
      else(level EQUAL 0)
        message(STATUS "** ${ARGN} **")
      endif()
    endif()
  endfunction()
  set(FetchLevel 0)
  vprint(0 "Fetching (${FetchLevel}): ${library}")
  math(EXPR FetchLevel "${FetchLevel}+1")

  # Identify the branch for other dependency downloads
  set(savedDetailsPropertyName "_FetchBoostContent_${library}_savedDetails")
  get_property(
    alreadyDefined GLOBAL
    PROPERTY ${savedDetailsPropertyName}
    DEFINED)
  if(NOT alreadyDefined)
    message(
      FATAL_ERROR "_FetchBoostContent_${library}_savedDetails should be defined"
    )
  endif()
  get_property(DeclaredArgs GLOBAL PROPERTY ${savedDetailsPropertyName})
  set(oneValueArgs GIT_TAG HG_TAG CVS_TAG)
  cmake_parse_arguments(ARG "" "${oneValueArgs}" "" ${DeclaredArgs})
  set(libs_BRANCH master)
  foreach(tag ${ARG_GIT_TAG} ${ARG_HG_TAG} ${ARG_CVS_TAG})
    if(tag)
      set(libs_BRANCH ${tag})
    endif()
  endforeach()
  string(REGEX MATCH "^(boost-[0-9]+.[0-9]+.[0-9]+)$" m1 ${libs_BRANCH})
  string(REGEX MATCH "^(boost-[0-9]+.[0-9]+.[0-9]+).beta1$" m2 ${libs_BRANCH})
  if(NOT m1
     AND NOT m2
     AND NOT libs_BRANCH STREQUAL develop)
    set(libs_BRANCH master)
  endif()
  vprint(0 "Boost tag: ${libs_BRANCH}")

  # Read the exceptions file exceptions.txt is the output of "boostdep
  # --list-exceptions" and it's part of the boostdep project. We download this
  # file from the appropriate branch and cache it.
  vprint(1 "Reading exceptions.txt")
  if(NOT EXISTS ${CMAKE_BINARY_DIR}/boost_exceptions.txt)
    file(
      DOWNLOAD
      "https://raw.githubusercontent.com/boostorg/boostdep/${libs_BRANCH}/depinst/exceptions.txt"
      "${CMAKE_BINARY_DIR}/boost_exceptions.txt")
  endif()
  file(READ "${CMAKE_BINARY_DIR}/boost_exceptions.txt" f)
  string(REGEX REPLACE ";" "\\\\;" f "${f}")
  string(REGEX REPLACE "\n" ";" f "${f}")
  foreach(line ${f})
    string(STRIP ${line} line)
    string(REGEX MATCH "(.*):$" m ${line})
    if(CMAKE_MATCH_COUNT)
      string(REPLACE "~" "/" module ${CMAKE_MATCH_1})
    else()
      set(header ${line})
      set(exception_${header} ${module})
      list(APPEND exception_headers ${header})
    endif()
  endforeach()

  # Aggregate all source dirs
  set(SOURCE_DIRS ${${library}_SOURCE_DIR})
  set(BINARY_DIRS ${${library}_BINARY_DIR})

  # Function to fetch modules
  function(fetch_modules)
    cmake_parse_arguments(ARG "" "" "MODULES" ${ARGN})
    set(modules ${ARG_MODULES})

    if(modules)
      vprint(0 "Fetching (${FetchLevel}): ${modules}")
      math(EXPR FetchLevel "${FetchLevel}+1")
      set(FetchLevel
          ${FetchLevel}
          PARENT_SCOPE)

      foreach(module ${modules})
        vprint(1 "Fetch ${module}")
        __fetchboostcontent_sanitize_name(${module} module)

        # Check properties
        set(savedDetailsPropertyName
            "_FetchBoostContent_${module}_savedDetails")
        get_property(
          alreadyDefined GLOBAL
          PROPERTY ${savedDetailsPropertyName}
          DEFINED)

        # Declare if not declared
        if(NOT alreadyDefined)
          string(FIND ${module} boost_ idx)
          if(idx EQUAL 0)
            string(SUBSTRING ${module} 6 -1 repo)
          else()
            set(repo ${module})
          endif()
          fetchboostcontent_declare(
            ${module}
            GIT_REPOSITORY
            https://github.com/boostorg/${repo}
            GIT_TAG
            ${libs_BRANCH}
            GIT_SHALLOW
            ON)
        endif()

        # Populate if not populated
        FetchContent_GetProperties(${module})
        if(NOT ${module}_POPULATED)
          FetchContent_Populate(${module})
        endif()

        # Remember source dir
        if(NOT ${${module}_SOURCE_DIR} IN_LIST SOURCE_DIRS)
          list(APPEND SOURCE_DIRS ${${module}_SOURCE_DIR})
          list(APPEND BINARY_DIRS ${${module}_BINARY_DIR})
          set(SOURCE_DIRS
              ${SOURCE_DIRS}
              PARENT_SCOPE)
          set(BINARY_DIRS
              ${BINARY_DIRS}
              PARENT_SCOPE)
        endif()
      endforeach()
    endif()
  endfunction()

  # Function to scan module dependencies
  function(module_for_header header OUT_VARIABLE)
    if(header IN_LIST exception_headers)
      set(${OUT_VARIABLE}
          boost_${exception_${header}}
          PARENT_SCOPE)
    else()
      # Identify modules from include, but we cannot ensure ${m} is a module
      # because we don't have access to the super-project here
      set(EXPRESSIONS
          # boost/function.hpp
          "(boost/[^\\./]*)\\.h[a-z]*$"
          # boost/numeric/conversion.hpp
          "(boost/numeric/[^\\./]*)\\.h[a-z]*$"
          # boost/numeric/conversion/header.hpp
          "(boost/numeric/[^/]*)/"
          # boost/function/header.hpp
          "(boost/[^/]*)/")
      foreach(exp ${EXPRESSIONS})
        string(REGEX MATCH ${exp} m ${header})
        if(CMAKE_MATCH_COUNT)
          string(REPLACE "/" "_" module ${CMAKE_MATCH_1})
          set(${OUT_VARIABLE}
              ${module}
              PARENT_SCOPE)
          return()
        endif()
      endforeach()
      set(${OUT_VARIABLE} PARENT_SCOPE)
      vprint(0 "Cannot determine module for header ${h}")
    endif()
  endfunction()

  function(scan_directory module dir)
    # Parse arguments
    vprint(1 "Scanning module ${module}")
    set(multiValueArgs DEPS SCAN_ONLY)
    cmake_parse_arguments(ARG "" "" "${multiValueArgs}" ${ARGN})
    vprint(1 "Scanning directory ${dir}")
    if(NOT ARG_DEPS)
      message(FATAL_ERROR "scan_directory: no DEPS argument")
    else()
      set(deps ${ARG_DEPS})
    endif()

    # Scanning include dir
    if(dir MATCHES "/include$")
      set(scanning_include_dir ON)
    endif()

    # Optimization: Scan only the headers we are actually including
    set(scan_only ${ARG_SCAN_ONLY})

    # Optimization: Dependencies are moved to front of the list so they
    # represent what targets should be created first. This is list of deps we
    # have already moved before the current ${module}. One thing to notice is,
    # theoretically, the order of these targets shouldn't matter in CMake.
    set(moved_deps ${module})

    # Try to use the cache file first
    set(cache_file ${dir}/dependencies.txt)
    if(EXISTS ${cache_file} AND NOT ignore_cache)
      file(READ ${cache_file} module_deps)
      foreach(mod ${module_deps})
        if(NOT mod IN_LIST deps)
          vprint(1 "Adding dependency ${mod}")
          list(PREPEND deps ${mod} 0)
        elseif(NOT mod IN_LIST moved_deps)
          # ensure dep comes before module to indicate dependency
          list(FIND deps ${module} this_idx)
          list(FIND deps ${mod} idx)
          if(idx GREATER this_idx)
            vprint(2 "Moving dependency ${mod}")
            list(REMOVE_AT deps ${idx})
            list(GET deps ${idx} v)
            list(REMOVE_AT deps ${idx})
            list(PREPEND deps ${mod} ${v})
            list(APPEND moved_deps ${mod})
          endif()
        endif()
      endforeach()
      set(DIR_DEPS
          ${deps}
          PARENT_SCOPE)
      return()
    endif()

    # Create list of files we are going to scan
    if(scan_only)
      foreach(file ${scan_only})
        list(APPEND files "${dir}/${file}")
      endforeach()
      vprint(2 "Scan only ${scan_only}")
    else()
      file(GLOB_RECURSE files "${dir}/*")
    endif()
    set(scanned_files ${files})

    # Scan files for dependencies the first time
    while(files)
      set(next_files)
      foreach(file ${files})
        list(APPEND scanned_files ${file})
        file(RELATIVE_PATH relative_path ${dir} ${file})
        vprint(2 "Scanning file ${relative_path}")

        # Scan header dependencies
        file(READ "${file}" contents)
        string(REGEX REPLACE ";" "\\\\;" contents "${contents}")
        string(REGEX REPLACE "\n" ";" contents "${contents}")
        foreach(line ${contents})
          string(STRIP "${line}" line)
          string(REGEX MATCH
                       "[ \\t]*#[ \\t]*include[ \\t]*[\"<](boost/[^\">]*)[\">]"
                       _ "${line}")
          if(CMAKE_MATCH_COUNT)
            set(header ${CMAKE_MATCH_1})
            module_for_header(${header} line_module)
            if(line_module)
              # Add this header to the list of dependency headers, regardless of
              # the module
              if(prune_dependencies AND NOT header IN_LIST
                                        included_headers_${line_module})
                list(APPEND included_headers_${line_module} ${header})
                list(APPEND modules_with_new_headers ${line_module})
                # This might mean we have more files to scan right now
                set(file_to_scan ${dir}/${header})
                if(scanning_include_dir
                   AND line_module STREQUAL module
                   AND NOT file_to_scan IN_LIST scanned_files)
                  list(APPEND next_files ${file_to_scan})
                endif()
              endif()

              # Include the new module in the list of dependencies for the
              # current module This is used to cache the submodule dependencies
              # later
              if(NOT line_module IN_LIST module_deps)
                list(APPEND module_deps ${line_module})
              endif()

              # Include the new module in the list of dependencies for the main
              # module This is what the main application is worried about
              if(NOT line_module IN_LIST deps)
                vprint(1 "Adding dependency ${line_module}")
                list(PREPEND deps ${line_module} 0)
              elseif(NOT line_module IN_LIST moved_deps)
                # Even if it was already in the list of dependencies we ensure
                # dep comes before the current module to indicate a dependency
                list(FIND deps ${module} this_idx)
                list(FIND deps ${line_module} idx)
                if(idx GREATER this_idx)
                  vprint(1 "Moving dependency ${line_module} (${file})")
                  list(REMOVE_AT deps ${idx})
                  list(GET deps ${idx} v)
                  list(REMOVE_AT deps ${idx})
                  list(PREPEND deps ${line_module} ${v})
                  list(APPEND moved_deps ${line_module})
                endif()
              endif()
            endif()
          endif()
        endforeach()
      endforeach()
      # If we found new files related to this very same module, we also need to
      # scan them
      set(files ${next_files})
      list(APPEND scanned_files ${next_files})
    endwhile()

    # Cache dependencies for this module dir
    if(NOT EXISTS ${cache_file} AND NOT ignore_cache)
      file(WRITE ${cache_file} "${module_deps}")
    endif()

    # Return new deps to parent scope
    set(DIR_DEPS
        ${deps}
        PARENT_SCOPE)

    # Return modules for which we found new headers and which are the new
    # headers
    set(DIR_MODULES_WITH_NEW_HEADERS
        ${modules_with_new_headers}
        PARENT_SCOPE)
    foreach(module ${modules_with_new_headers})
      set(DIR_INCLUDED_HEADERS_${module}
          ${included_headers_${module}}
          PARENT_SCOPE)
    endforeach()
  endfunction()

  function(scan_module_dependencies module)
    vprint(1 "Scanning module ${module}")
    set(options SCAN_ALL)
    set(multiValueArgs DEPS DIRS)
    cmake_parse_arguments(ARG "${options}" "" "${multiValueArgs}" ${ARGN})
    set(scan_all ${ARG_SCAN_ALL})
    set(deps ${ARG_DEPS})
    set(dirs ${ARG_DIRS})

    # Ensure library is populated
    FetchContent_GetProperties(${module})
    if(NOT ${module}_POPULATED)
      FetchContent_Populate(${module})
      message(FATAL_ERROR "${module} has not been populated yet")
    endif()
    if(NOT EXISTS ${${module}_SOURCE_DIR})
      message(FATAL_ERROR "${${module}_SOURCE_DIR} not found")
    endif()

    # Scan the include directory last
    if(include IN_LIST dirs)
      list(REMOVE_ITEM dirs include)
      list(APPEND dirs include)
    endif()

    # Scan directories
    foreach(dir ${dirs})
      if(EXISTS ${${module}_SOURCE_DIR}/${dir})
        if(NOT scan_all
           AND dir STREQUAL include
           AND prune_dependencies
           AND included_headers_${module})
          scan_directory(${module} ${${module}_SOURCE_DIR}/${dir} DEPS
                         ${ARG_DEPS} SCAN_ONLY ${included_headers_${module}})
        else()
          scan_directory(${module} ${${module}_SOURCE_DIR}/${dir} DEPS
                         ${ARG_DEPS})
        endif()
        # Update deps
        set(ARG_DEPS ${DIR_DEPS})

        # Update the modules for which we found need headers
        foreach(module ${DIR_MODULES_WITH_NEW_HEADERS})
          if(NOT module IN_LIST modules_with_new_headers)
            list(APPEND modules_with_new_headers ${module})
          endif()
          foreach(header ${DIR_INCLUDED_HEADERS_${module}})
            if(NOT header IN_LIST included_headers_${module})
              list(APPEND included_headers_${module} ${header})
            endif()
          endforeach()
        endforeach()
      endif()
    endforeach()

    # Return new deps
    set(MODULE_DEPS
        ${ARG_DEPS}
        PARENT_SCOPE)

    # Return modules for which we found new headers and which are the new
    # headers
    set(MODULE_MODULES_WITH_NEW_HEADERS
        ${modules_with_new_headers}
        PARENT_SCOPE)
    foreach(module ${modules_with_new_headers})
      set(MODULE_INCLUDED_HEADERS_${module}
          ${included_headers_${module}}
          PARENT_SCOPE)
    endforeach()
  endfunction()

  function(fetch_module_dependencies)
    cmake_parse_arguments(ARG "" "" "DEPS" ${ARGN})
    set(deps ${ARG_DEPS})

    # Extract modules to install and mark them as installed in deps
    set(deps_copy ${deps})
    while(deps_copy)
      list(POP_FRONT deps_copy module installed)
      if(installed EQUAL 0)
        list(APPEND modules ${module})
        list(FIND deps ${module} idx)
        if(idx EQUAL -1)
          message(FATAL_ERROR "Cannot find ${module} in dependencies")
        else()
          list(REMOVE_AT deps ${idx})
          list(REMOVE_AT deps ${idx})
          list(INSERT deps ${idx} ${module} 1)
        endif()
      endif()
    endwhile()

    # Return here if there are no modules to fetch
    if(NOT modules)
      set(MODULES_LENGTH
          0
          PARENT_SCOPE)
      set(FETCH_DEPS
          ${deps}
          PARENT_SCOPE)
      return()
    endif()

    # Fetch all modules and return dirs to the caller
    fetch_modules(MODULES ${modules})
    set(FetchLevel
        ${FetchLevel}
        PARENT_SCOPE)
    set(SOURCE_DIRS
        ${SOURCE_DIRS}
        PARENT_SCOPE)
    set(BINARY_DIRS
        ${BINARY_DIRS}
        PARENT_SCOPE)

    # Scan these module dependencies for the next round
    if(NOT all_retrieved_from_cache)
      vprint(2 "scan_modules")
      foreach(module ${modules})
        scan_module_dependencies(${module} DEPS ${deps} DIRS include src)
        set(deps ${MODULE_DEPS})
        # Update the modules for which we found headers we need
        foreach(module ${MODULE_MODULES_WITH_NEW_HEADERS})
          if(NOT module IN_LIST modules_with_new_headers)
            list(APPEND modules_with_new_headers ${module})
          endif()
          foreach(header ${MODULE_INCLUDED_HEADERS_${module}})
            if(NOT header IN_LIST included_headers_${module})
              list(APPEND included_headers_${module} ${header})
            endif()
          endforeach()
        endforeach()
      endforeach()
    endif()

    # Return
    list(LENGTH modules modules_size)
    set(MODULES_LENGTH
        ${modules_size}
        PARENT_SCOPE)
    set(FETCH_DEPS
        ${deps}
        PARENT_SCOPE)

    # Update modules for which we found new headers in the parent context
    foreach(module ${modules_with_new_headers})
      set(${included_headers_${module}}
          ${included_headers_${module}}
          PARENT_SCOPE)
    endforeach()
  endfunction()

  # Set initial list of modules and dirs
  set(module ${library})
  set(deps ${module} 1)
  set(dirs include src)
  foreach(dir ${exclude})
    list(REMOVE_ITEM dirs ${dir})
  endforeach()
  foreach(dir ${include})
    list(APPEND dirs ${dir})
  endforeach()

  # Check if we already have the dependencies in a cache file
  if(NOT prune_dependencies)
    set(all_deps_cache_file ${${name}_SOURCE_DIR}/dependencies.txt)
    set(init_all_deps_cache_file ${all_deps_cache_file})
    if(NOT EXISTS ${all_deps_cache_file})
      set(init_all_deps_cache_file
          ${${name}_SOURCE_DIR}/pruned_dependencies.txt)
    endif()
  else()
    set(all_deps_cache_file ${${name}_SOURCE_DIR}/pruned_dependencies.txt)
    set(init_all_deps_cache_file ${all_deps_cache_file})
  endif()
  if(EXISTS ${init_all_deps_cache_file} AND NOT ignore_cache)
    if(init_all_deps_cache_file STREQUAL all_deps_cache_file)
      set(all_retrieved_from_cache TRUE)
    endif()
    file(READ ${init_all_deps_cache_file} module_deps)
    foreach(mod ${module_deps})
      if(mod STREQUAL module)
        continue()
      endif()
      if(NOT mod IN_LIST deps)
        vprint(1 "Adding dependency ${mod}")
        list(PREPEND deps ${mod} 0)
      endif()
    endforeach()
  else()
    # Scan dependencies of the main library to get dep level 1
    vprint(1 "Directories to scan: ${dirs}")
    # Fix scanning of modules whose headers are not being used
    scan_module_dependencies(${module} DEPS ${deps} DIRS ${dirs} SCAN_ALL)
    set(deps ${MODULE_DEPS})

    # Remove any deps that should be ignored
    foreach(dep ${ignore})
      if(dep IN_LIST deps)
        vprint(1 "Ignoring dependency ${dep}")
        list(FIND deps ${dep} idx)
        if(NOT idx EQUAL -1)
          list(REMOVE_AT deps ${idx})
          list(REMOVE_AT deps ${idx})
          unset(included_headers_${module_with_new_headers})
        endif()
      endif()
    endforeach()

    foreach(module_with_new_headers ${MODULE_MODULES_WITH_NEW_HEADERS})
      foreach(header ${MODULE_INCLUDED_HEADERS_${module_with_new_headers}})
        if(NOT header IN_LIST included_headers_${module_with_new_headers})
          list(APPEND included_headers_${module_with_new_headers} ${header})
        endif()
      endforeach()
    endforeach()
  endif()

  # Fetch dependencies for all other levels
  vprint(2 "Dependencies: ${deps}")
  fetch_module_dependencies(DEPS ${deps})
  set(deps ${FETCH_DEPS})
  while(MODULES_LENGTH)
    fetch_module_dependencies(DEPS ${deps})
    set(deps ${FETCH_DEPS})
  endwhile()

  # Sort directories according to the level
  set(is_dep ON)
  foreach(module ${deps})
    if(is_dep)
      list(APPEND all_deps ${module})
      # Sort dependencies by level
      FetchContent_GetProperties(${module})
      if(${module}_POPULATED)
        if(${module}_SOURCE_DIR IN_LIST SOURCE_DIRS)
          list(APPEND all_src_dirs ${${module}_SOURCE_DIR})
          list(REMOVE_ITEM SOURCE_DIRS ${${module}_SOURCE_DIR})
        endif()
        if(${module}_BINARY_DIR IN_LIST BINARY_DIRS)
          list(APPEND all_bin_dirs ${${module}_BINARY_DIR})
          list(REMOVE_ITEM BINARY_DIRS ${${module}_BINARY_DIR})
        endif()
      endif()
      set(is_dep OFF)
    else()
      set(is_dep ON)
    endif()
  endforeach()
  list(PREPEND SOURCE_DIRS ${all_src_dirs})
  list(PREPEND BINARY_DIRS ${all_bin_dirs})

  # Cache all dependencies for this main module
  if(NOT EXISTS ${all_deps_cache_file} AND NOT ignore_cache)
    file(WRITE ${all_deps_cache_file} "${all_deps}")
  endif()

  # Return directories to the caller
  set(${library}_DEPS
      ${all_deps}
      PARENT_SCOPE)
  set(${library}_SOURCE_DIRS
      ${SOURCE_DIRS}
      PARENT_SCOPE)
  set(${library}_BINARY_DIRS
      ${BINARY_DIRS}
      PARENT_SCOPE)
endfunction()

# Attempt to use FetchContent_MakeAvailable for any boost library that works
# with add_subdirectory and its dependencies. Not many Boost libraries do work
# with add_subdirectory but the user can still try. In the future, we can
# attempt to adapt this function to get around boost limitations.
function(FetchBoostContent_MakeAvailable contentName)
  # Check if population has already been performed
  fetchboostcontent_getproperties(${contentName})
  if(NOT ${contentName}_POPULATED)
    # Fetch the content using previously declared details
    fetchboostcontent_populate(${contentName})

    # Bring the populated content into the build In this case of Boost
    # libraries, we are including the directory and the dependency directories.
    # This means a second call to this function might try this include a
    # directory we have already included. We have a few strategies to avoid
    # this. - In this variant, we avoid including the dependencies for which
    # there's a target already defined, because we can't include the same
    # subdirectory twice - We also mark the directories we have included here to
    # ensure we don't include them twice
    set(src_dirs ${${contentName}_SOURCE_DIRS})
    set(bin_dirs ${${contentName}_BINARY_DIRS})
    set(deps ${${contentName}_DEPS})
    while(src_dirs AND deps)
      list(POP_FRONT src_dirs src_dir)
      list(POP_FRONT bin_dirs bin_dir)
      list(POP_FRONT deps dep)
      if(NOT TARGET ${dep})
        set(dirIncludedPropertyName
            "_FetchBoostContent_MakeAvailable_${dep}_included")
        get_property(
          alreadyIncluded GLOBAL
          PROPERTY ${dirIncludedPropertyName}
          DEFINED)
        if(NOT alreadyIncluded)
          set_property(GLOBAL PROPERTY ${dirIncludedPropertyName} 1)
          if(EXISTS ${src_dir}/CMakeLists.txt)
            add_subdirectory(${src_dir} ${bin_dir})
          endif()
          if(NOT TARGET boost_headers)
            add_library(boost_headers INTERFACE)
            add_library(Boost::headers ALIAS boost_headers)
          endif()
          get_target_property(boost_headers_imported boost_headers IMPORTED)
          if(NOT boost_headers_imported)
            target_include_directories(
              boost_headers SYSTEM
              INTERFACE "$<BUILD_INTERFACE:${src_dir}/include/>")
            set_property(
              TARGET boost_headers
              APPEND
              PROPERTY boost_target_install_dir "${src_dir}/include/")
          endif()
        endif()
      endif()
    endwhile()
  endif()
endfunction()
