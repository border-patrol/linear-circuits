module HalfAdderLin
  ( input  logic a
  , input  logic b
  , output logic carry
  , output logic res
  );

   wire logic a1;
   wire logic a2;
   split s0(a1,a2,a);

   wire logic b1;
   wire logic b2;
   split s1(b1,b2,b);

   xor g1(res,a1,b1);
   and g2(carry,a2,b2);

endmodule;
