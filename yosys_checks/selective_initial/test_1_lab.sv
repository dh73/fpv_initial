
module test_1 (
    input clk, 
    output reg x, y) ;
    initial
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
                assume ((x == y)) ;
            end
endmodule


