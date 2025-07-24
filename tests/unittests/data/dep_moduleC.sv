module moduleC;
    // Module C depends on B
    moduleB instB();
    initial $display("Module C");
endmodule
