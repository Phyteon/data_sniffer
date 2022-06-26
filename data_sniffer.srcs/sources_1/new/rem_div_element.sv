`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.06.2022 16:32:13
// Design Name: 
// Module Name: rem_div_element
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


module rem_div_element #(
        byte unsigned BYTE_POSITION =  'x
    )
    (
        input
            wire clk,
            wire nreset,
            wire [7:0] single_byte,
        output
            reg [15:0] remainder
    );
    localparam MULTIPLY_COEFF = 2**(BYTE_POSITION * 8) % 'd97;
    /* Some functionality is hardcoded for now, should be generated in the future */
    
    /* Internal signals */
    wire [7:0] single_byte_remainder;
    reg [15:0] multiplied_by_offset;
    
    /* Logic */
    
    assign single_byte_remainder = (('d97 > single_byte) ?
                        single_byte : 
                        ((('d194 > single_byte) && ('d97 <= single_byte)) ?
                            single_byte - 'd97 : single_byte - 'd194));
    
    generate
        case(MULTIPLY_COEFF)
            'd35: multiplier mult_by_35(.clk(clk), .num_in(single_byte_remainder), .result(multiplied_by_offset));
            'd36: multiplier mult_by_36(.clk(clk), .num_in(single_byte_remainder), .result(multiplied_by_offset));
            'd61: multiplier mult_by_61(.clk(clk), .num_in(single_byte_remainder), .result(multiplied_by_offset));
            'd62: multiplier mult_by_62(.clk(clk), .num_in(single_byte_remainder), .result(multiplied_by_offset));
            'd96: multiplier mult_by_96(.clk(clk), .num_in(single_byte_remainder), .result(multiplied_by_offset));
        endcase
    endgenerate
    
    always @(posedge clk) begin
        if (1'b0 == nreset)
            remainder <= 0;
        else
            remainder <= multiplied_by_offset;
    end
    
    
    
    
    
endmodule
