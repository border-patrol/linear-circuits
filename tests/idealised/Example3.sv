module Example2( input  logic[2] ab
               , output logic    c
               );

   wire logic    as (aOut, aIn);
   wire logic[1] as (bOutV, bInV);

   first(aOut, bOutV, ab);

   wire logic as (bOut, bIn);

   extract(bOut, bInV);

   and(c, aIn, bIn);

endmodule;
