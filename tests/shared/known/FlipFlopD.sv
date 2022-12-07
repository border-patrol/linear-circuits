module FlipFlopD
  ( input logic i
  , input logic clock
  , output logic o
  , output logic oinv
  );

   wire logic notI;

   not n(notI,i);

   wire logic na1o;
   nand na1(na1o,i,clock);

   wire logic na2o;
   nand na2(na2o,notI,clock);

   nand na3(o,oinv,na1o);

   nand na4(oinv,o,na2o);


endmodule; // FlipFlopD
