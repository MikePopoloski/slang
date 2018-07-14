# slang - cmake entry point
cmake_minimum_required(VERSION 3.11)
project(slang VERSION 0.1.0 LANGUAGES CXX)

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
	add_compile_options(/Gy)

	if(CMAKE_BUILD_TYPE MATCHES DEBUG)
		add_compile_options(/GS)	# Buffer overrun checks
	endif()
else()
	set(CMAKE_CXX_STANDARD 17)
	set(CMAKE_CXX_STANDARD_REQUIRED ON)
	set(CMAKE_CXX_EXTENSIONS OFF)
endif()

add_subdirectory(source)
add_subdirectory(tools)
add_subdirectory(tests/unittests)