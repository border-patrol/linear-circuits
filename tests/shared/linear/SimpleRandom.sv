module SimpleRandom( output logic out
              , input logic a
              , input logic b
              , input logic c
              , input logic d
               );

   wire logic x;
   wire logic y;

   and gate_1(x, a, b);
   or gate_2(y, c, d);
   xor gate_3(out, x, y);
endmodule;
