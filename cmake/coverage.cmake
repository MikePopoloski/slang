# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

set(COVERAGE_GCOV_TOOL
    "gcov"
    CACHE STRING "Name of the gcov binary to run")

set(COVERAGE_TRACE_COMMAND
    lcov -c -q -o "${PROJECT_BINARY_DIR}/coverage.info" --gcov-tool
    ${COVERAGE_GCOV_TOOL} -d "${PROJECT_BINARY_DIR}" --include
    "${PROJECT_SOURCE_DIR}/source/*" --include
    "${PROJECT_SOURCE_DIR}/include/slang/*" --config-file
    "${PROJECT_SOURCE_DIR}/.lcovrc"
    CACHE STRING
          "; separated command to generate a trace for the 'coverage' target")

set(COVERAGE_HTML_COMMAND
    genhtml "${PROJECT_BINARY_DIR}/coverage.info" -p "${PROJECT_SOURCE_DIR}" -o
    "${PROJECT_BINARY_DIR}/coverage_html" --ignore-errors inconsistent
    --ignore-errors corrupt
    CACHE
      STRING
      "; separated command to generate an HTML report for the 'coverage' target"
)

add_custom_target(
  coverage
  COMMAND ${COVERAGE_TRACE_COMMAND}
  COMMAND ${COVERAGE_HTML_COMMAND}
  COMMENT "Generating coverage report"
  VERBATIM)
