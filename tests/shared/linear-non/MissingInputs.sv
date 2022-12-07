module MissingInputs( output logic    out
              , input  logic[2:0] ab
              );

   nand n1(out, ab[0], ab[1]);

endmodule;
