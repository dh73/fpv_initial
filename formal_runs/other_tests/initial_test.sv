`default_nettype none
  module initial_test(input wire clk,
		      output logic rstn_dly);

   // VERIFIC-ERROR [VERI-1763] initial_test.sv:8: SVA directive is not sensitive to any clock
   default clocking fpv_clk @(posedge clk); endclocking
     
   bit [1:0] tmp;
   initial begin
`ifdef _SV_SUPPORT_
      a0: assume property(@(posedge clk) &tmp);
      a1: assert property(@(posedge clk) rstn_dly);
`endif
      a0: assume (tmp == 2'b11);
      a1: assert (rstn_dly);
   end
   
   always_ff @(posedge clk) begin
      tmp <= {tmp[1], 1'b1};
   end
   assign rstn_dly = tmp[1];
   
   af: assert property(@(posedge clk) rstn_dly);
endmodule // initial_test

