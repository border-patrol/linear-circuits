module Example( output logic out
              , input  logic i0
              , input  logic i1
              , input  logic i2
              , input  logic i3
              , input  logic s1
              , input  logic s0
                );

   wire logic y0;
   wire logic y1;
   wire logic y2;
   wire logic y3;
   wire logic s1n;
   wire logic s0n;

   not n1(s1n, s1);
   not n2(s0n, s0);
//   and alpha(y0, i0, s1n, s0n);
//   and beta(y1, i1, s1n, s0);
//   and gamma(y2, i2, s1, s0n);
//   and terra(y3, i3, s1, s0);
//   or out2(out, y0, y1, y2, y3);

endmodule;
