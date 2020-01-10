# Find all the public headers of the slang project, the only one we currently document
file(GLOB_RECURSE SLANG_PUBLIC_HEADERS ${PROJECT_SOURCE_DIR}/include/*.h)
file(GLOB_RECURSE SLANG_DOX_FILES ${PROJECT_SOURCE_DIR}/docs/*.dox)

set(DOXYGEN_INPUT_DIR "${PROJECT_SOURCE_DIR}/include ${PROJECT_SOURCE_DIR}/docs")
set(DOXYGEN_EXTERNAL_DIR "${PROJECT_SOURCE_DIR}/external")
set(DOXYGEN_STRIP_PATH "${PROJECT_SOURCE_DIR}/include")
set(DOXYGEN_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR})
set(DOXYGEN_INDEX_FILE ${DOXYGEN_OUTPUT_DIR}/html/index.html)
set(DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)
set(DOXYFILE_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)

configure_file(${DOXYFILE_IN} ${DOXYFILE_OUT} @ONLY)

add_custom_command(OUTPUT ${DOXYGEN_INDEX_FILE}
                   DEPENDS ${SLANG_PUBLIC_HEADERS} ${SLANG_DOX_FILES}
                   COMMAND ${Python_EXECUTABLE} ${PROJECT_SOURCE_DIR}/scripts/rmdir.py ${CMAKE_CURRENT_BINARY_DIR}/html
                   COMMAND ${Python_EXECUTABLE} ${PROJECT_SOURCE_DIR}/scripts/rmdir.py ${CMAKE_CURRENT_BINARY_DIR}/xml
                   COMMAND ${Python_EXECUTABLE} ${DOXYGENPY_PATH} ${DOXYFILE_OUT}
                   MAIN_DEPENDENCY ${DOXYFILE_OUT} ${DOXYFILE_IN}
                   COMMENT "Generating docs"
                   VERBATIM)

add_custom_target(docs ALL DEPENDS ${DOXYGEN_INDEX_FILE})