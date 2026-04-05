// First definition: module named mux_primitive.
// With --allow-module-redef this definition wins over any later redefinitions.
module mux_primitive(Y, S, A, B);
  output Y;
  input S, A, B;
  assign Y = S ? B : A;
endmodule
