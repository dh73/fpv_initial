
`default_nettype none
module ex2 #(parameter ABSTRACT = 1) (
    input wire [7:0] vlda, vldb, 
    input wire [7:0][15:0] taga, tagb, 
    input wire clk, rstn) ;
    logic [7:0] valid ; 
    initial
        begin
            if (ABSTRACT) 
                begin
                    ac0 : assume property (@(posedge clk) disable iff ( (!rstn)) (valid == 8'b11111111)) ;// valid logic is asserted during first clock.
                    for (int i = 0 ; (i < 8) ; i ++ )
                        ap0 : assert property (@(posedge clk) disable iff ( (!rstn)) (taga[i] != tagb[i])) ;
                end
        end
    assign valid[0] = (((!vlda[0]) | (!vldb[1])) | (taga[0] != tagb[0])) ; 
    assign valid[1] = (((!vlda[1]) | (!vldb[1])) | (taga[1] != tagb[1])) ; 
    assign valid[2] = (((!vlda[2]) | (!vldb[1])) | (taga[2] != tagb[2])) ; 
    assign valid[3] = (((!vlda[3]) | (!vldb[1])) | (taga[3] != tagb[3])) ; 
    assign valid[4] = (((!vlda[4]) | (!vldb[1])) | (taga[4] != tagb[4])) ; 
    assign valid[5] = (((!vlda[5]) | (!vldb[1])) | (taga[5] != tagb[5])) ; 
    assign valid[6] = (((!vlda[6]) | (!vldb[1])) | (taga[6] != tagb[6])) ; 
    assign valid[7] = (((!vlda[7]) | (!vldb[1])) | (taga[7] != tagb[7])) ; 
    always
        @(*)
        if ($initstate()) 
            begin
                if (ABSTRACT) 
                    begin
                        ac0 : assume property (@(posedge clk) disable iff ( (!rstn)) (valid == 8'b11111111)) ;// valid logic is asserted during first clock.
                        for (int i = 0 ; (i < 8) ; i ++ )
                            ap0 : assert property (@(posedge clk) disable iff ( (!rstn)) (taga[i] != tagb[i])) ;
                    end
            end

// ex2
endmodule


