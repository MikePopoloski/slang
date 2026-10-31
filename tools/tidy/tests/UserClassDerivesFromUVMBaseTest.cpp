// SPDX-FileCopyrightText: Srinivasan Venkataramanan
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

// Minimal stand-in for the UVM library, including an unprefixed class like UVM's get_t.
static std::string withUVM(std::string_view body) {
    return R"(
package uvm_pkg;
    virtual class uvm_object;
    endclass

    virtual class uvm_component extends uvm_object;
    endclass

    class uvm_driver #(type REQ = int) extends uvm_component;
    endclass

    class uvm_sequence_item extends uvm_object;
    endclass

    class get_t;
    endclass
endpackage

import uvm_pkg::*;
)" + std::string(body);
}

static bool uvmCheck(std::string_view body) {
    return runCheckTest("UserClassDerivesFromUVMBase", withUVM(body));
}

TEST_CASE("UserClassDerivesFromUVMBase: UVM library classes are not flagged") {
    CHECK(uvmCheck(""));
}

TEST_CASE("UserClassDerivesFromUVMBase: class with no base class") {
    CHECK_FALSE(uvmCheck(R"(
class helper_c;
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: class chain with no UVM base class") {
    CHECK_FALSE(uvmCheck(R"(
class base_c;
endclass

class derived_c extends base_c;
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: direct UVM base class") {
    CHECK(uvmCheck(R"(
class my_item extends uvm_sequence_item;
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: multi-level chain to a parameterized UVM base class") {
    CHECK(uvmCheck(R"(
class my_item extends uvm_sequence_item;
endclass

class company_driver extends uvm_driver #(my_item);
endclass

class custom_driver extends company_driver;
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: unresolved base class is not flagged") {
    CHECK(uvmCheck(R"(
class my_c extends not_declared_c;
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: interface class and UVM-derived implementer") {
    CHECK(uvmCheck(R"(
interface class my_api;
    pure virtual function void f();
endclass

class my_comp extends uvm_component implements my_api;
    virtual function void f();
    endfunction
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: implementing an interface class is not a UVM base class") {
    CHECK_FALSE(uvmCheck(R"(
interface class my_api;
    pure virtual function void f();
endclass

class my_impl implements my_api;
    virtual function void f();
    endfunction
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: generic class without UVM base class") {
    CHECK_FALSE(uvmCheck(R"(
class my_q #(type T = int);
endclass

class my_comp extends uvm_component;
    my_q #(int) q1;
    my_q #(byte) q2;
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: generic class with parameterized UVM base class") {
    CHECK(uvmCheck(R"(
class my_item extends uvm_sequence_item;
endclass

class my_drv #(type T = int) extends uvm_driver #(T);
endclass

class my_comp extends uvm_component;
    my_drv #(my_item) d;
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: built-in std classes are not flagged") {
    CHECK(uvmCheck(R"(
class my_item extends uvm_sequence_item;
endclass

class my_comp extends uvm_component;
    mailbox #(my_item) mbx;
    semaphore sem;
    process p;
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: nested class without UVM base class") {
    CHECK_FALSE(uvmCheck(R"(
class my_comp extends uvm_component;
    class helper_c;
    endclass
endclass
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: class declared in a module") {
    CHECK_FALSE(uvmCheck(R"(
module top;
    class mod_local_c;
    endclass
endmodule
)"));
}

TEST_CASE("UserClassDerivesFromUVMBase: diagnostic text and location") {
    std::string output;
    auto result = runCheckTest("UserClassDerivesFromUVMBase", R"(
class helper_c;
endclass
)",
                               {}, &output);

    CHECK_FALSE(result);

    CHECK("\n" + output == R"(
source:2:7: warning: [UVM-36] class 'helper_c' does not derive from any UVM base class
class helper_c;
      ^
)");
}
