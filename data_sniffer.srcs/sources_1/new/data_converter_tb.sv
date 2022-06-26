`timescale 1ns / 1ns
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.06.2022 17:32:42
// Design Name: 
// Module Name: data_converter_tb
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


module data_converter_tb();
/* Internal signals */
logic clk;
logic nreset;
logic [7:0] data_in_reg;
wire [7:0] data_in;
wire [7:0] data_out;

byte unsigned char_idx = 0;
byte unsigned char = 0;

byte unsigned char_tab [256];

/* Module under test */

data_converter converter(.clk(clk), .nreset(nreset), .data_chunk(data_in), .data_processed(data_out));

initial begin
    for (int i = 0; i < 256; i++) begin
        char_tab[char] = char;
        char += 1;
    end
end

initial clk <= 1'b0;
initial begin
    nreset <= 1'b0;
    #5 nreset <= 1'b1;
end

assign data_in = data_in_reg;

always #5 clk <= ~clk;

always @(posedge clk) begin
    data_in_reg = char_tab[char_idx];
    char_idx += 1;
    $display("Char input: %s, processed output (from prev cycle): %d", data_in, data_out);
end


endmodule
