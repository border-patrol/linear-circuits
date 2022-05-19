module Example0( input  logic a
               , input  logic b
               , output logic c);

   wire logic as (o,i);

   and(o,a,b);

   not(c,i);

endmodule;
