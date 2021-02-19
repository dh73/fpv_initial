`default_nettype none
module ex0
  (output logic ready,
   input wire clk, rstn);
   
   logic      ft;
   
   initial begin
      // Assertion evaluated only once: ready is initially low
      assert property (@(posedge clk) disable iff (!rstn) !ready);
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
