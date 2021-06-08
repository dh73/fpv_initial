
module test_2 (
    input clk, foo, 
    output reg x, y) ;
    initial
        begin
            assume (foo) ;
            if (foo) 
                assume ((x == y)) ;
        end
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


