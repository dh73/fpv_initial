`default_nettype none
module fifo_nobind #(parameter DW = 64, NUM_ENTRIES = 32)
   (output logic empty, full,
    output logic [DW-1:0] data_out,
    input wire [DW-1:0]   data_in,
    input wire 		  clk,
    input wire 		  rstn,
    input wire 		  push,
    input wire 		  pop);

   // This is the regfile of DWxNUM_ENTRIES
   var logic [DW-1:0] regfile [0:NUM_ENTRIES-1];
   // Write and read pointers.
   localparam SIZE = $clog2(NUM_ENTRIES);
   var logic [SIZE-1:0] rd_ptr_ps, wr_ptr_ps;
   logic [SIZE-1:0]     rd_ptr_ns, wr_ptr_ns;
   var logic 		empty_ps, full_ps;
   logic 		empty_ns, full_ns;

   // FIFO Controller
   always_ff @(posedge clk) begin
      /* If reset, clear full, set empty,
       * return read and write pointers to
       * the corresponding site. */
      if(!rstn) begin
	 empty_ps <= 1'b1;
	 full_ps <= 1'b0;
	 rd_ptr_ps <= {SIZE{1'b0}};
	 wr_ptr_ps <= {SIZE{1'b0}};
      end
      else begin
	 empty_ps <= empty_ns;
	 full_ps <= full_ns;
	 rd_ptr_ps <= rd_ptr_ns;
	 wr_ptr_ps <= wr_ptr_ns;
      end // else: !if(!rstn)
   end // always_ff @ (posedge clk)

   always_comb begin
      empty_ns = empty;
      full_ns = full;
      rd_ptr_ns = rd_ptr_ps;
      wr_ptr_ns = wr_ptr_ps;
      /* If push and not full, increment wr_ptr,
       * set empty to zero. */
      if(push && !full) begin
	 empty_ns = 1'b0;
	 wr_ptr_ns = wr_ptr_ps + 1'b1;
	 // If both pointers match, fifo is full.
	 if(wr_ptr_ps + 1'b1 == rd_ptr_ps)
	   full_ns = 1'b1;
      end
      /* If pop and not empty, increment rd_ptr,
       * set full to zero. */
      if(pop && !empty) begin
	 full_ns = 1'b0;
	 rd_ptr_ns = rd_ptr_ps + 1'b1;
	 // If both pointers match, fifo is empty.
	 if(wr_ptr_ps == rd_ptr_ps + 1'b1)
	   empty_ns = 1'b1;
      end
   end // always_comb
   always_ff @(posedge clk) begin
      if (push && !full) regfile[wr_ptr_ps] <= data_in;
   end
   always_comb begin
      data_out = regfile[rd_ptr_ps];
   end

   assign full = full_ps;
   assign empty = empty_ps;

   default clocking fpv_clk @(posedge clk); endclocking
   default disable iff (!rstn);

   /********* Structural properties **********/
   // Original test
   // [a]ssume [b]ound [n] bound magnitude
`ifdef _SV_SUPPORT_
   initial begin
      ab1_rdptr: assume property(rd_ptr_ps == 'd0);
      ab1_empty: assume property(empty_ps  == 1'b1);
      ab1_full:  assume property(full_ps == 1'b0);
   end
`else
   initial begin
      ab1_rdptr: assume(rd_ptr_ps == 'd0);
      ab1_empty: assume(empty_ps  == 1'b1);
      ab1_full:  assume(full_ps == 1'b0);
   end
`endif

   // A more "advanced" test
   // For the initial assumptions
   // Make the wr pointer free:
   // [[This needs to be done in the SBY file]]
   // Ensure the wr pointer is inside the valid range:
`ifdef _SV_SUPPORT_
   initial ab1_wrptr: assume property(wr_ptr_ps <= SIZE);
`else
   initial ab1_wrptr: assume(wr_ptr_ps <= SIZE);
`endif
   // Start from where wrprt is able to write, invalidating values
   // smaller than wrptr. This is to reach deeper states/decrease
   // proof convergence time.
   initial begin
      foreach(regfile[i]) begin
`ifdef _SV_SUPPORT_
	 ab1_regfile: assume property(wr_ptr_ps > i |-> regfile[i] == i);
`else
	 ab1_regfile: assume(!(wr_ptr_ps > i) || regfile[i] == i);
`endif
      end
   end
   // If we insert cutpoints to the regfile, the test gets even more abstracted
   /***************** Datapath properties *****************/
   // For universal quantification
   logic [DW-1:0] D;
   observed_d: assume property(1'b1 ##1 $stable(D));

   bit 		  incr;
   bit 		  decr;
   bit 		  can_read;
   bit [SIZE-1:0] minus;
   var bit [SIZE-1:0] count, iptr;
   var bit 	      sampled_in, sampled_out;

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
   assign minus = wr_ptr_ps - rd_ptr_ps;
   assign iptr = rd_ptr_ps + count - 1'b1;

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
   L4: assume property(sampled_in && !sampled_out |-> ##1 regfile[iptr] == D);

   // Helper properties to enforce induction cases (for SBY only)
   H0: assume property(empty |-> ##1 !pop);
   H1: assume property(full |-> ##1 !push);

   // Hard to prove property
   LN: assert property(can_read && !sampled_out |-> data_out == D);
endmodule // fifo
