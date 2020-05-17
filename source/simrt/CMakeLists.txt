add_library(simrt
    "IO.cpp"
    "SimRT.cpp"
)

target_compile_options(simrt PRIVATE ${SLANG_WARN_FLAGS})
target_include_directories(simrt PUBLIC ../../include/)
