module BVEdgesBad ( output logic      o
                  , input  logic[1:0] i);

   wire logic indirect1;
   wire logic indirect2;

   assign indirect1 = i[0];
   assign indirect2 = i[1];

   and a(o,indirect1,indirect2);

endmodule; // BVEdges
