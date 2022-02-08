module Example9( inout logic[1:0] out
               , input logic      bc
               );

   nand n1(out[0], bc, bc);

endmodule;
