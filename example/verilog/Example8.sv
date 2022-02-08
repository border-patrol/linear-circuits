module Example5( inout logic      out
               , inout logic[1:0] bc
               );

   nand n1(out, bc[0], bc[1]);

endmodule;
