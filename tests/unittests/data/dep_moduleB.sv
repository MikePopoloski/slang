module moduleB;
    // Module B depends on A
    moduleA instA();
    initial $display("Module B");
endmodule
