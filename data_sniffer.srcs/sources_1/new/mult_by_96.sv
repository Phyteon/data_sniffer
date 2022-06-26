`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.06.2022 22:56:01
// Design Name: 
// Module Name: mult_by_96
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


module mult_by_96(
    input
        wire clk,
        wire [7:0] num_in,
    output
        shortint unsigned result
    );
    
    /* Internal signals */
    wire [15:0] num_by_bit_5;
    wire [15:0] num_by_bit_6;
    wire [15:0] result_comb;
    
    `ifdef SIMULATION_ENV
    reg [7:0] prev_num_in;
    `endif
    
    /* Logic */
    assign num_by_bit_5 = num_in << 5;
    assign num_by_bit_6 = num_in << 6;
    assign result_comb = num_by_bit_5 + num_by_bit_6;
    
    always @(posedge clk) begin
        `ifdef SIMULATION_ENV
        prev_num_in <= num_in;
        `endif
        result <= result_comb;
    end
    
    `ifdef SIMULATION_ENV
    property pr__mult_by_96__correct_result_latched;
        always @(posedge clk)
            (!$isunknown(num_in))
            |-> ##1
            result == prev_num_in * 96;
    endproperty
    
    as__mult_by_61__correct_result_latched:
        assert property(pr__mult_by_96__correct_result_latched)
            else
            $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
    `endif
endmodule
