module test_1 (
	input clk,
	output reg x, y
);
	initial assume (x == y);
	always @(posedge clk) begin
		x <= !y;
		y <= !x;
		assert (x == y);
	end
endmodule
module test_2 (
	input clk, foo,
	output reg x, y
);
	initial begin
		assume (foo);
		if (foo)
			assume (x == y);
	end
	always @(posedge clk) begin
		x <= !y;
		y <= !x;
		assert (x == y);
	end
endmodule
module test_3 (
	input clk, foo,
	output reg x, y
);
	initial assume (foo);
	initial if (foo) assume (x == y);
	always @(posedge clk) begin
		x <= !y;
		y <= !x;
		assert (x == y);
	end
endmodule
