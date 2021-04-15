
class uvm_resource_db #(type T);
  static function bit read_by_name(inout T val);
    return 1;
  endfunction
endclass

interface clk_gen_if(
    output bit       valid,
    output bit       clk,
    input      [7:0] out,
    output bit [7:0] in
);
endinterface: clk_gen_if

module env;
    virtual clk_gen_if m_if;
    function void connect_phase();
        assert(uvm_resource_db#(virtual clk_gen_if)::read_by_name(m_if));
    endfunction: connect_phase
endmodule
