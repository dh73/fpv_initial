
module test_3 (
    input clk, foo, 
    output reg x, y) ;
    initial
        assume (foo) ;
    initial
        if (foo) 
            assume ((x == y)) ;
    always
        @(posedge clk)
        begin
            x <=  (!y) ;
            y <=  (!x) ;
            assert ((x == y)) ;
        end
    always
        @(*)
        if ($initstate()) 
            begin
                assume (foo) ;
                if (foo) 
                    assume ((x == y)) ;
            end
endmodule


