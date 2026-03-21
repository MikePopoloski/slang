// sv_add is declared here as an extern "C" symbol; at JIT link time it is
// resolved to the SystemVerilog function exported via `export "DPI-C"`.
extern "C" {

extern int sv_add(int a, int b);

int c_combine(int a, int b) {
    return sv_add(a, b) + a * b;
}

} // extern "C"
