find_package(Doxygen REQUIRED)

# Find all the public headers of the slang project, the only one we currently document
get_target_property(SLANG_PUBLIC_HEADER_DIR slang INTERFACE_INCLUDE_DIRECTORIES)
file(GLOB_RECURSE SLANG_PUBLIC_HEADERS ${SLANG_PUBLIC_HEADER_DIR}/*.h)

set(DOXYGEN_INPUT_DIR "${PROJECT_SOURCE_DIR}/include ${PROJECT_SOURCE_DIR}/source")
set(DOXYGEN_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/docs/doxygen)
set(DOXYGEN_INDEX_FILE ${DOXYGEN_OUTPUT_DIR}/html/index.html)
set(DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)
set(DOXYFILE_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)

configure_file(${DOXYFILE_IN} ${DOXYFILE_OUT} @ONLY)

file(MAKE_DIRECTORY ${DOXYGEN_OUTPUT_DIR}) # Doxygen won't create this for us
 
add_custom_command(OUTPUT ${DOXYGEN_INDEX_FILE}
                   DEPENDS ${SLANG_PUBLIC_HEADERS}
                   COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYFILE_OUT}
                   MAIN_DEPENDENCY ${DOXYFILE_OUT} ${DOXYFILE_IN}
                   COMMENT "Generating docs")
 
add_custom_target(Doxygen ALL DEPENDS ${DOXYGEN_INDEX_FILE})