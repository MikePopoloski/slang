// Second definition of the same name as a primitive.
// Without --allow-module-redef this triggers a hard Redefinition error
// because the kind (primitive) differs from the first definition (module).
primitive mux_primitive(Y, S, A, B);
  output Y;
  input S, A, B;
  table
    0 0 ? : 0 ;
    0 1 ? : 1 ;
    1 ? 0 : 0 ;
    1 ? 1 : 1 ;
  endtable
endprimitive
