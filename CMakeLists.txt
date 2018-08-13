# slang - cmake entry point
cmake_minimum_required(VERSION 3.10)
project(slang VERSION 0.1.0 LANGUAGES CXX)

option(SLANG_MSVC_W4 "Enable /W4 for MSVC builds" ON)
option(SLANG_MSVC_STATIC_RUNTIME "Enable linking to the MSVC static runtime" ON)
option(SLANG_COVERAGE "Enable code coverage" OFF)
set(SLANG_SANITIZERS "" CACHE STRING "List of Clang sanitizers to include in build")

# Default build type if none is set
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE "Release" CACHE STRING
      "Build type (Release/Debug/RelWithDebInfo/MinSizeRel)" FORCE)
endif()

# Defaults for a bunch of Windows-specific junk
if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  add_definitions(-DNOMINMAX)
  add_definitions(-DUNICODE)
  add_definitions(-D_UNICODE)
  add_definitions(-DWIN32_LEAN_AND_MEAN)
  add_definitions(-DNTDDI_VERSION=0x06010000)
  add_definitions(-D_WIN32_WINNT=0x0601)
  add_definitions(-D_SCL_SECURE_NO_WARNINGS)
  add_definitions(-D_CRT_SECURE_NO_WARNINGS)
  add_definitions(-D_CRT_SECURE_NO_DEPRECATE)
endif()

# Always require C++17 or later, no extensions
if(CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
	# Prefer the latest standard, and enable full conformance
	add_compile_options(/std:c++latest)
	add_compile_options(/permissive-)
	add_compile_options(/Zc:inline)
	add_compile_options(/Gy)		# Function-level linking

	# Ignore warnings in external headers
	add_compile_options(/experimental:external /external:anglebrackets /external:W0 /external:templates-)

	if(CMAKE_BUILD_TYPE MATCHES "Debug")
		# Use fast linking
		string(REGEX REPLACE "/debug" "/DEBUG:FASTLINK" CMAKE_EXE_LINKER_FLAGS_DEBUG "${CMAKE_EXE_LINKER_FLAGS_DEBUG}")
		string(REGEX REPLACE "/debug" "/DEBUG:FASTLINK" CMAKE_SHARED_LINKER_FLAGS_DEBUG "${CMAKE_SHARED_LINKER_FLAGS_DEBUG}")
	else()
		add_compile_options(/GS-)	# Disable buffer overrun checks
		add_compile_options(/GL)	# Whole program optimization
		add_compile_options(/Zi)	# Generate debug info even in release

		set(REL_LINK_FLAGS "/LTCG /DEBUG:FULL /INCREMENTAL:NO /OPT:REF /OPT:ICF")
		set(CMAKE_EXE_LINKER_FLAGS "${MAKE_EXE_LINKER_FLAGS} ${REL_LINK_FLAGS}")
		set(CMAKE_SHARED_LINKER_FLAGS "${MAKE_SHARED_LINKER_FLAGS} ${REL_LINK_FLAGS}")
		set(CMAKE_STATIC_LINKER_FLAGS "${MAKE_SHARED_LINKER_FLAGS} /LTCG")
	endif()

	if(SLANG_MSVC_W4)
		if(CMAKE_CXX_FLAGS MATCHES "/W[0-4]")
			string(REGEX REPLACE "/W[0-4]" "/W4" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
		else()
			set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /W4")
		endif()
	endif()

	if(SLANG_MSVC_STATIC_RUNTIME)
		set(variables
			CMAKE_C_FLAGS_DEBUG
			CMAKE_C_FLAGS_MINSIZEREL
			CMAKE_C_FLAGS_RELEASE
			CMAKE_C_FLAGS_RELWITHDEBINFO
			CMAKE_CXX_FLAGS_DEBUG
			CMAKE_CXX_FLAGS_MINSIZEREL
			CMAKE_CXX_FLAGS_RELEASE
			CMAKE_CXX_FLAGS_RELWITHDEBINFO
		)
		foreach(variable ${variables})
			if(${variable} MATCHES "/MD")
				string(REGEX REPLACE "/MD" "/MT" ${variable} "${${variable}}")
			endif()
		endforeach()
	endif()
else()
	set(CMAKE_CXX_STANDARD 17)
	set(CMAKE_CXX_STANDARD_REQUIRED ON)
	set(CMAKE_CXX_EXTENSIONS OFF)

	# Always include debug info
	add_compile_options(-g)

	# Color in diagnostics please
	if(CMAKE_GENERATOR MATCHES "Ninja")
		if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
			add_compile_options(-Xclang -fcolor-diagnostics)
		else()
  			add_compile_options(-fdiagnostics-color)
  		endif()
  	endif()

  	if(SLANG_COVERAGE)
  		add_compile_options(--coverage -fno-omit-frame-pointer -fno-optimize-sibling-calls)
  		link_libraries(--coverage)

		if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
			add_compile_options(-O0 -fno-inline-functions)
		else()
			add_compile_options(
			    -fno-inline
				-fno-inline-small-functions
				-fno-default-inline
			)
		endif()
	endif()

	if(SLANG_SANITIZERS)
		add_compile_options("-fsanitize=${SLANG_SANITIZERS}")
		link_libraries("-fsanitize=${SLANG_SANITIZERS}")
	endif()
endif()

if(CMAKE_GENERATOR MATCHES "Visual Studio")
	# Only MSBuild needs this, other generators will compile one file at a time
  	add_compile_options("/MP")
endif()

# Install dependencies via conan
include(cmake/conan.cmake)
conan_cmake_run(CONANFILE conanfile.txt BASIC_SETUP CMAKE_TARGETS)

add_subdirectory(source)
add_subdirectory(tools)

include(CTest)

add_subdirectory(tests/unittests)
add_subdirectory(tests/regression)
