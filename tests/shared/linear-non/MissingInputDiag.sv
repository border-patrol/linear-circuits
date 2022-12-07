module MissingInputDiag( output logic           out
              , input  logic[1:0][1:0] bc
                );

   nand n1(out, bc[0][1], bc[1][0]);

endmodule;
