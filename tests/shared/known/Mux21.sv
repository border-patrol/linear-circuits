module Mux21
  ( input  logic a
  , input  logic b
  , input  logic select
  , output logic res
  );

   wire logic snot;
   wire logic ao;
   wire logic bo;

   not n1(snot,select);
   and a1(ao, snot,a);
   and a2(bo, select,b);

   or a3(res,ao,bo);

endmodule; // Mux21
