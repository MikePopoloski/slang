# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# Fetch the RTLMeter benchmark suite. RTLMeter ships all RTL source files inside
# the repository itself, so no additional downloads are required after this
# step.
FetchContent_Declare(
  rtlmeter
  GIT_REPOSITORY https://github.com/MikePopoloski/rtlmeter
  GIT_TAG main
  GIT_SHALLOW ON)
FetchContent_MakeAvailable(rtlmeter)
