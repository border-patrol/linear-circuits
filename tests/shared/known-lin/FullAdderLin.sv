module FullAdderLin
  ( input  logic a
  , input  logic b
  , input  logic carryIn
  , output logic carryOut
  , output logic res
  );

   wire logic a1;
   wire logic a2;
   split s0(a1,a2,a);

   wire logic b1;
   wire logic b2;
   split s1(b1,b2,b);

   wire logic x1;
   wire logic x1a;
   wire logic x1b;
   split s2(x1a,x1b,x1);

   wire logic c1;
   wire logic c2;
   split s3(c1,c2,carryIn);


   wire logic x2;
   wire logic x3;

   xor g1(x1,a1,b1);
   and g2(x3,a2,b2);

   xor g3(res,x1a,c1);
   and g4(x2,x1b,c2);

   or g5(carryOut,x2,x3);

endmodule;
