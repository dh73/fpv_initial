// setting OP to ^ (XOR) will make the formal property pass
`define OP +

module fmdemo  (
	input clock,
	output reg [31:0] state
);
	reg [31:0] next_state;
	always_comb begin
		next_state = state;
		next_state = next_state `OP (next_state << 13);
		next_state = next_state `OP (next_state >> 17);
		next_state = next_state `OP (next_state << 5);
	end

	always @(posedge clock) begin
		state <= next_state;
	end

	initial assume (state != 0);
	always_comb assert (state != 0);
endmodule
