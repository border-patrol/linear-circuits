module Example5( input  logic[5] abcde
               , output logic[2]    ab
               , output logic       c
               , output logic[2]    de
               );

   index[2](c,ab,de,abcde);

endmodule;
