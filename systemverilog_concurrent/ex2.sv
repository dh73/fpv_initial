`default_nettype none
module ex2 #(parameter ABSTRACT = 1)
  (input wire [7:0] vlda, vldb,
   input wire [7:0][15:0] taga, tagb,
   input wire 		  clk, rstn);

   logic [7:0] valid;
   
   initial begin 
      if (ABSTRACT) 
	assume property (@(posedge clk) disable iff (!rstn)
			 valid == 8'hff); // valid logic is asserted
                                          // during first clock. 
   end

   genvar i;
   for (i = 0; i < 8; i++) begin
      assign valid[i] = (!vlda[i] | !vldb[1] | (taga[i] != tagb[i]));
   end
endmodule // ex2


   
