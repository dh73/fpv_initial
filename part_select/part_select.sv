`default_nettype none
module part_select #(parameter MAGIC = 8)
   (output logic      unlock,
    input  wire [1:0] kind);

   logic [7:0] test [3:0];
   logic [3:0] rt;

   initial $readmemb("init.bin", test);

   initial begin
      if (test[1][4] && test[3][4]) assume (kind == 2'b10);
      else assume (kind == 2'b11);
   end

   assign unlock = (rt == (test[1][3:0]+test[3][3:0]));

   always_comb begin
      rt = 4'b0;
      if (kind == 2'b10) begin
	 rt = MAGIC;
	 assert (unlock);
      end
      else assert (0);
   end

endmodule // param_select
