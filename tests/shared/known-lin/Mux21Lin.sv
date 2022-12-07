module Mux21Lin
  ( input  logic a
  , input  logic b
  , input  logic select
  , output logic res
  );

   wire logic sa;
   wire logic sb;
   split s0(sa,sb,select);

   wire logic snot;
   wire logic ao;
   wire logic bo;

   not n1(snot,sa);

   and a1(ao, snot,a);
   and a2(bo, sb,b);

   or a3(res,ao,bo);

endmodule;
