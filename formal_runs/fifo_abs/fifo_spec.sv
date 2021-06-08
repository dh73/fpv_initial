`default_nettype none
bind fifo fifo_spec dut (.*);
module fifo_spec #(parameter DW = 64, NUM_ENTRIES = 32)
   (input wire empty, full,
    input wire [DW-1:0] data_out,
    input wire [DW-1:0] data_in,
    input wire [DW-1:0] debug_regfile [0:NUM_ENTRIES-1],
    input wire 		clk,
    input wire 		rstn,
    input wire 		push,
    input wire 		pop);

   default clocking fpv_clk @(posedge clk); endclocking
   default disable iff (!rstn);

   /********* Structural properties **********/
   // Original test
   // [a]ssume [b]ound [n] bound magnitude
`ifdef _SV_SUPPORT_
   initial begin
      ab1_rdptr: assume property(fifo.rd_ptr_ps == 'd0);
      ab1_empty: assume property(fifo.empty_ps  == 1'b1);
      ab1_full:  assume property(fifo.full_ps == 1'b0);
   end
`else
    initial begin
      ab1_rdptr: assume(fifo.rd_ptr_ps == 'd0);
      ab1_empty: assume(fifo.empty_ps  == 1'b1);
      ab1_full:  assume(fifo.full_ps == 1'b0);
    end
`endif

   // A more "advanced" test
   // For the initial assumptions
   // Make the wr pointer free:
   // [[This needs to be done in the SBY file]]
   // Ensure the wr pointer is inside the valid range:
`ifdef _SV_SUPPORT_
   initial ab1_wrptr: assume property(fifo.wr_ptr_ps <= fifo.SIZE);
`else
   initial ab1_wrptr: assume(fifo.wr_ptr_ps <= fifo.SIZE);
`endif
   // Start from where wrprt is able to write, invalidating values
   // smaller than wrptr. This is to reach deeper states/decrease
   // proof convergence time.
   initial begin
      foreach(fifo.regfile[i]) begin
`ifdef _SV_SUPPORT_
	 ab1_regfile: assume property(fifo.wr_ptr_ps > i |-> fifo.regfile[i] == i);
`else
	 ab1_regfile: assume(!(fifo.wr_ptr_ps > i) || fifo.regfile[i] == i);
`endif
      end
   end
   // If we insert cutpoints to the regfile, the test gets even more abstracted
   /***************** Datapath properties *****************/
   // For universal quantification
   logic [DW-1:0] D;
   observed_d: assume property(1'b1 ##1 $stable(D));

   localparam SIZE = $clog2(NUM_ENTRIES);
   bit 		  incr;
   bit 		  decr;
   bit 		  can_read;
   bit [SIZE-1:0] minus;
   var bit [SIZE-1:0] count, iptr;
   var bit sampled_in, sampled_out;

   // More initial assumptions for the induction test
   initial begin
`ifdef _SV_SUPPORT_
      ab1_count: assume property(count == 'd0);
      ab1_smpi:  assume property(sampled_in == 1'd0);
      ab1_smpo:  assume property(sampled_out == 1'd0);
`else
      ab1_count: assume(count == 'd0);
      ab1_smpi:	 assume(sampled_in == 1'd0);
      ab1_smpo:	 assume(sampled_out == 1'd0);
`endif
   end

   assign incr = push && !full && !sampled_in;
   assign decr = pop && !empty && !sampled_out;
   assign minus = fifo.wr_ptr_ps - fifo.rd_ptr_ps;
   assign iptr = fifo.rd_ptr_ps + count - 1'b1;

   always_ff @(posedge clk) begin
      if (!rstn) count <= {SIZE{1'b0}};
      else       count <= count + incr - decr;
   end

   always_ff @(posedge clk) begin
      if (!rstn) begin
	 sampled_in <= {DW{1'b0}};
	 sampled_out <= {DW{1'b0}};
      end
      else begin
	 sampled_in <= sampled_in || (data_in == D && incr);
	 sampled_out <= sampled_out || (can_read);
      end
   end
   assign can_read = count == 1 && sampled_in && decr;

   /* The following properties are already proven
    * as inductive invariants. Removing them makes it
    * really hard for the solver to converge on property
    * LN. */
   L1: assume property(!sampled_in |-> !sampled_out);
   L2: assume property(sampled_in && sampled_out |-> ##1 count == 0);
   L3: assume property(!sampled_in |-> ##1 count == (minus));
   L4: assume property(sampled_in && !sampled_out |-> ##1 debug_regfile[iptr] == D);

   // Helper properties to enforce induction cases (for SBY only)
   H0: assume property(empty |-> ##1 !pop);
   H1: assume property(full |-> ##1 !push);

   // Hard to prove property
   LN: assert property(can_read && !sampled_out |-> data_out == D);
endmodule // fifo_spec
