module Example4( output logic    out
               , input  logic[2] ab
               );

   nand n1(out, ab[0], ab[1]);

endmodule;
