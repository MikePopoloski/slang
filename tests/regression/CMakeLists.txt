add_test(NAME regression_delayed_reg COMMAND driver -E "${CMAKE_CURRENT_LIST_DIR}/delayed_reg.v")
add_test(NAME regression_wire_module COMMAND driver -E "${CMAKE_CURRENT_LIST_DIR}/wire_module.v")
