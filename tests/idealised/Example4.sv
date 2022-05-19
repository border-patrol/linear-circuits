module Example4( input  logic[4] abcd
               , output logic    ab
               , output logic    cd
               );

   wire logic as (aOut, aIn);
   wire logic as (bOut, bIn);
   wire logic as (cOut, cIn);
   wire logic as (dOut, dIn);

   wire logic[3] as (bcdOut, bcdIn);

   first(aOut, bcdOut, abcd);

   wire logic[1] as (bOutV, bInV);
   wire logic[1] as (dOutV, dInV);

   index[1](cOut, bOutV, dOutV, bcdIn);

   extract(bOut, bInV);
   extract(dOut, dInV);

   and(ab, aIn, bIn);
   and(cd, cIn, dIn);

endmodule;
