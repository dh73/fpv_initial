`default_nettype none
module property_equivalence (input bit clk);
   wire a, b;
   initial ab1_a: assert property (@(posedge clk) 
				   (not(a[*] ##1 b)
		                    iff strong(!b[+] ##0 !a)));
endmodule // property_equivalence

