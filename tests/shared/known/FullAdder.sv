module FullAdder
  ( input  logic a
  , input  logic b
  , input  logic carryIn
  , output logic carryOut
  , output logic res
  );

   wire logic x1;
   wire logic x2;
   wire logic x3;

   xor g1(x1,a,b);
   and g2(x3,a,b);

   xor g3(res,x1,carryIn);
   and g4(x2,x1,carryIn);

   or g5(carryOut,x2,x3);

endmodule; // FullAdder
