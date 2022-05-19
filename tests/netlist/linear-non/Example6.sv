module Example5( output logic    out
               , input  logic    a
               , input  logic[2:0] bc
               );

   nand n1(out, a, bc[1]);

endmodule;
