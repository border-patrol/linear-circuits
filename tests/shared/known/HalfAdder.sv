module HalfAdder
  ( input  logic a
  , input  logic b
  , output logic carry
  , output logic res
  );


   xor g1(res,a,b);
   and g2(carry,a,b);


endmodule; // HalfAdder
