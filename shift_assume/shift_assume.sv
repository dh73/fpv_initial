`default_nettype none
module shift_assume
  (output logic [31:0] out,
   input wire [31:0] a, b);

   logic [3:0] first_clock;
   
   function [15:0] apply_mask;
      input logic [15:0] tmpx;
      begin 
	 apply_mask = tmpx >> 1;
      end
   endfunction // apply_mask
   
   initial begin
      logic [15:0] tmpa, tmpb;
      tmpa = apply_mask(16'hfff0);
      tmpb = apply_mask(16'h00e4);
      assume (a == tmpa);
      assume (b == tmpb);
   end

   
   always_comb begin
      out = a * b;
      assert (out == 32'h38fc70);
   end
   
endmodule // shift_assume


