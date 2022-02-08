module Example2( input  logic a
               , input  logic b
               , input  logic cin
               , output logic cout
               , output logic s
               );

   wire logic as (adupO1, adupI1);
   wire logic as (adupO2, adupI2);

   wire logic as (bdupO1, bdupI1);
   wire logic as (bdupO2, bdupI2);

   copy(adupO1, adupO2, a);
   copy(bdupO1, bdupO2, b);

   wire logic as (xO, xI);
   wire logic as (xdupO1, xdupI1);
   wire logic as (xdupO2, xdupI2);

   copy(xdupO1,xdupO2,xI);
   xor(xO, adupI2, bdupI2);


   wire logic as (cdupO1, cdupI1);
   wire logic as (cdupO2, cdupI2);

   copy(cdupO1,cdupO2,cin);

   wire logic as (ao1,ai1);
   wire logic as (ao2,ai2);

   and(ao1,xdupI1,cdupI1);
   and(ao2,adupI1,bdupI1);

   xor(s,cdupI2,xdupI2);

   ior(cout, ai1, ai2);

endmodule;
