`default_nettype none
module fifo #(parameter DW = 64, NUM_ENTRIES = 32)
   (output logic empty, full,
    output logic [DW-1:0] data_out,
    output logic [DW-1:0] debug_regfile [0:NUM_ENTRIES-1],
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
      debug_regfile = regfile;
   end

   assign full = full_ps;
   assign empty = empty_ps;
endmodule // fifo
