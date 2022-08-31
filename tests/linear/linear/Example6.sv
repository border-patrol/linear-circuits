module Example7( output logic    o
               , input  logic    i
               );

   wire logic temp;
   wire logic temp2;

   assign temp = i;

   assign temp2 = temp;

   assign o = temp2;

endmodule;
