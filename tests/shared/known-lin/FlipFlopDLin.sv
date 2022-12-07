module FlipFlopDLin
  ( input logic i
  , input logic clock
  , output logic o
  , output logic oinv
  );

   wire logic iA;
   wire logic iB;

   split s1(iA,iB,i);

   wire logic clockA;
   wire logic clockB;

   split s2(clockA,clockB,clock);

   wire logic notI;

   not n(notI,iA);

   wire logic na1o;
   nand na1(na1o,iB,clockA);

   wire logic na2o;
   nand na2(na2o,notI,clockB);

   wire logic q;
   wire logic qAlt;
   wire logic qinv;
   wire logic qinvAlt;

   nand na3(q,qinvAlt,na1o);

   nand na4(qinv,qAlt,na2o);

   split s3(o,qAlt,q);
   split s4(oinv,qinvAlt,qinv);

endmodule;
