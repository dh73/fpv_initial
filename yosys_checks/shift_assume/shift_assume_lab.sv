
`default_nettype none
module shift_assume (
    output logic [31:0] out, 
    input wire [31:0] a, b) ;
    function [15:0] apply_mask ; 
    // apply_mask
        input logic [15:0] tmpx ; 
        begin
            apply_mask = (tmpx >> 1) ;
        end
    endfunction
    initial
        begin
            logic [15:0] tmpa, tmpb ; 
            tmpa = apply_mask(16'b1111111111110000) ;
            tmpb = apply_mask(16'b011100100) ;
            assume ((a == tmpa)) ;
            assume ((b == tmpb)) ;
            assert ((out == 32'b01110001111110001110000)) ;
        end
    always_comb
        begin
            out = (a * b) ;
            //assert (out == 32'h38fc70);
        end
    always
        @(*)
        if ($initstate()) 
            begin
                assume ((a == tmpa)) ;
                assume ((b == tmpb)) ;
                assert ((out == 32'b01110001111110001110000)) ;
            end

// shift_assume
endmodule


