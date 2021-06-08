`default_nettype none
module find_values
  (input bit [31:0] a,
   input bit [31:0] b,
   input bit        start,
   input bit        clk,
   output bit       done);

   initial begin 
	   a0: assume(done);
	   c0: cover property (@(posedge clk) ps == calc);
   end

   typedef enum logic [1:0] {st, calc, res} states_t;
   states_t ps, ns;

   always @(posedge clk) begin
      if(!start) ps <= st;
      else       ps <= ns;
   end

   logic [31:0] t0, t1, t2, t3;
   bit          t4;
   always @(*) begin
      ns = ps;
      done = 1'b0;
      case(ps)
        st: if(start) ns = calc;
        calc: begin
           t0 = a * b;
           t1 = a+b+'d674;
           t2 = a - 'd6;
           t3 = 'd4*(b-'d6);
           t4 = (t0 == t1) && (t2 == t3);
           if(t4) begin ns = res; done = 1'b1; end
           else ns = calc;
        end
        default: ns = st;
      endcase // case (ps)
   end // always @ (*)
   //ap: cover property (@(posedge clk) ps == calc ##1 ps == !calc);
endmodule // find_values
