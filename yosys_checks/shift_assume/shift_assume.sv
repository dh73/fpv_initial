`default_nettype none
module shift_assume
  (output logic [31:0] out,
   input wire [31:0] a, b);

   function [15:0] apply_mask;
      input logic [15:0] tmpx;
      begin
         apply_mask = tmpx >> 1;
      end
   endfunction // apply_mask

   logic [15:0] tmpa, tmpb;
   always_comb tmpa = apply_mask(16'hfff0);
   always_comb tmpb = apply_mask(16'h00e4);
   
   initial begin
      assume(a == tmpa);
      assume(b == tmpb);
      assert(out == 32'h38fc70);
   end

   always_comb begin
      out = a * b;
   end

endmodule // shift_assume




