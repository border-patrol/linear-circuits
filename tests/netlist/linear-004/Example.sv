module Example( output logic out
              , input  logic left
              , input  logic right
              );

   nand n1(out, left, right);

endmodule;
