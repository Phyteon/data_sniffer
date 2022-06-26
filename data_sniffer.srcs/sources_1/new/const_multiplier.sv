`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.06.2022 21:17:33
// Design Name: 
// Module Name: const_multiplier
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module const_multiplier#(
        byte unsigned COEFF = 'x
    )
    (
        input
            wire [7:0] number_in,
        output
            wire [15:0] number_out
    );
    
    /* Internal signals */
    generate
        genvar bit_idx;
    
        for (bit_idx = 0; bit_idx < 8; bit_idx++) begin: innets
            if ((COEFF & (8'b1 << bit_idx)) != 0) begin
                wire [7:0] num;
                assign num = number_in << bit_idx;
            end
        end: innets
    
    endgenerate
    
    
    always_comb begin
        
    end
endmodule
