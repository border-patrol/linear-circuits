module Example7( input  logic[1] a
               , output logic    b
               , output logic[1] c
               , input  logic    d
               );

   extract(b, a);
   insert(c, d);

endmodule;
