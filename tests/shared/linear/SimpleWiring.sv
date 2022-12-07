// adapted from https://bravelearn.com/verilog-gate-level-modeling-examples/
module SimpleWiring( output logic out
                   , input  logic a
                   , input  logic b
                   , input  logic c
                   , input  logic d
                   );

   wire logic x;
   wire logic y;

   or or1(x, a, b);
   or or2(y, c, d);
   or orfinal(out, x, y);

endmodule; // Example
