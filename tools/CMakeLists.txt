# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_subdirectory(driver)
add_subdirectory(hier)
add_subdirectory(netlist)
add_subdirectory(reflect)
add_subdirectory(rewriter)
add_subdirectory(tidy)

if(SLANG_INCLUDE_THREADTEST)
  add_subdirectory(threadtest)
endif()
