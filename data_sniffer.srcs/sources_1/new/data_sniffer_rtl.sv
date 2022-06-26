`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 19.06.2022 15:54:56
// Design Name: 
// Module Name: data_sniffer_rtl
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


module data_sniffer_rtl #(
        int DATA_BUS_BIT_WIDTH = 'x,
        int FIFO_CELL_LENGTH = 'x
    )
    (
        input
            wire clk, /* Clock signal */
            wire nreset, /* Negative reset */
            wire [DATA_BUS_BIT_WIDTH - 1:0] data_in, /* Input data from AXI Stream */
        output
            reg [7:0] recognised_data_type, /* Type of recognised data */
            reg [FIFO_CELL_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] recognised_data_out, /* Recognised data out */
            reg [7:0] recognised_data_beginning_position_in_stream, /* Beginning position in the stream */
            reg [7:0] recognised_data_frame_count /* Span */
    );
    /* Localparams */
    localparam int unsigned SWISS_CHECKSUM_DIVIDER = 'd97;
    localparam int unsigned POLISH_CHECKSUM_DIVIDER = 'd97;
    localparam SWISS_FORMAT_IBAN_LENGTH = 'd21;
    localparam POLISH_FORMAT_IBAN_LENGTH = 'd28;
    /* Internal signals */
    reg [FIFO_CELL_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] main_fifo;
    reg [SWISS_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] swiss_format_buffer_one;
    reg [SWISS_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] swiss_format_buffer_two;
    reg [POLISH_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] polish_format_buffer_one;
    reg [POLISH_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] polish_format_buffer_two;

    
endmodule
