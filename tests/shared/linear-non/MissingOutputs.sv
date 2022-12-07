module MissingOutputs( inout logic[1:0] out
              , input logic      b
              , input logic      c
              );

   nand n1(out[0], b, c);

endmodule;
