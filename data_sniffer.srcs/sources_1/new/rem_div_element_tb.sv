`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 27.06.2022 01:43:37
// Design Name: 
// Module Name: rem_div_element_tb
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


module rem_div_element_tb();

/* Internal signals */
logic clk;
logic nreset;

byte unsigned byte_table [256];
byte unsigned byte_idx;
reg [7:0] single_byte_0_reg;
reg [7:0] single_byte_1_reg;
wire [7:0] single_byte_0;
wire [7:0] single_byte_1;

reg [15:0] remainder_0;
reg [15:0] remainder_1;

/* DUT */
rem_div_element #(.BYTE_POSITION(0)) div_0(.clk(clk), .nreset(nreset), .single_byte(single_byte_0), .remainder(remainder_0));
rem_div_element #(.BYTE_POSITION(1)) div_1(.clk(clk), .nreset(nreset), .single_byte(single_byte_1), .remainder(remainder_1));

initial begin
    byte_idx = 0;
    clk = 1'b0;
    nreset = 1'b0;
    #5 nreset = 1'b1;
end

initial begin
    for (int i = 0; i < 256; i++) begin 
        byte_table[i] = i;
    end 
end 

always #5 clk = ~clk;

always @(posedge clk) begin
    single_byte_0_reg <= byte_table[byte_idx];
    single_byte_1_reg <= byte_table[byte_idx];
    byte_idx += 1;
end

assign single_byte_0 = single_byte_0_reg;
assign single_byte_1 = single_byte_1_reg;

endmodule
