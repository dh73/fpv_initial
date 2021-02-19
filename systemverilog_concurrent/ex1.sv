`default_nettype none
module ex1
  (output logic oreset,
   input wire clk, irstn);
   
   logic [1:0] ft;
   
   initial begin
      // Assertion evaluated only once: reset is high during first two cycles
      assert property (@(posedge clk) disable iff (!irstn) 
		       oreset and nexttime oreset);
   end
   always_ff @(posedge clk) begin
      if (!irstn) begin 
	 oreset <= 1'b0; 
	 ft <= 2'b0; 
      end
      else begin 
	 oreset <= !ft[0];
	 ft <= {ft[0], 1'b1};
      end
   end
   
endmodule // ex0
