`default_nettype none
module ex0
  (output logic ready,
   input wire clk, rstn);
   
   logic      ft;
   
   initial begin
      ac0: assume property(@(posedge clk) !rstn);
      // Assertion evaluated only once: ready is initially low
      ap0: assert property (@(posedge clk) !ready);
   end
   always_ff @(posedge clk) begin
      if (!rstn) begin 
	 ready <= 1'b0; 
	 ft <= 1'b0; 
      end
      else begin 
	 ready <= ft;
	 ft <= 1'b1;
      end
   end
   
endmodule // ex0
