`ifdef VERBOSE_SIM
    `define SIM_LOG_INFO(msg) $info("INFO at t=%t: %s", $time, msg)
    `define SIM_LOG_WARN(msg) $warning("WARNING at t=%t: %s", $time, msg)
    `define SIM_LOG_ERROR(msg) $error("ERROR at t=%t: %s", $time, msg)
`else
    `define SIM_LOG_INFO(msg)
    `define SIM_LOG_WARN(msg)
    `define SIM_LOG_ERROR(msg)
`endif

module data_sniffer #(
    int DATA_BUS_BIT_WIDTH = 'x,
    int FIFO_BYTE_LENGTH = 'x
    )
    (
    input
        wire clk, /* Clock signal */
        wire nreset, /* Negative reset */
        wire [DATA_BUS_BIT_WIDTH - 1:0] data_in, /* Input data from AXI Stream */
    output
        reg [7:0] recognised_data_type, /* Type of recognised data */
        reg [DATA_BUS_BIT_WIDTH - 1:0] recognised_data_out, /* Recognised data out */
        reg [7:0] recognised_data_beginning_position_in_stream, /* Beginning position in the stream */
        reg [7:0] recognised_data_frame_count /* Span */
    );
    localparam SIZEOF_UINT = $bits(int unsigned);
    localparam MAX_POSSIBLE_COUNTRY_CODE_VAL = 'd3535;
    localparam MIN_POSSIBLE_COUNTRY_CODE_VAL = 'd1010;
    reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] local_fifo;
    
    
    class DataSniffer #(int DATA_BUS_BIT_WIDTH = 'x, int FIFO_BYTE_LENGTH = 'x);
        local int unsigned swiss_checksum_divider = 'd97;
        local int unsigned polish_checksum_divider = 'd97;
        static function logic check_if_country_code_correct(input int unsigned country_code);
            if ((MAX_POSSIBLE_COUNTRY_CODE_VAL < country_code) || (MIN_POSSIBLE_COUNTRY_CODE_VAL > country_code)) begin
                `SIM_LOG_ERROR({"Unknown country code: ", string'(country_code)});
                return 1'b0;
            end
            else begin
                `SIM_LOG_INFO({"Country code in valid range: ", string'(country_code)});
                 return 1'b1;
            end
        endfunction
            
        static function logic [2:0] try_find_pattern(input int unsigned country_code,
            input reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] buffer);
            case (country_code)
                'd1217: return {1'b0, 1'b0, process_data_swiss_format(buffer)};
                'd2521: return {1'b0, 1'b1, process_data_polish_format(buffer)};
                default: return {3'b1};
            endcase
        endfunction
            
        static function int unsigned convert_raw_data_to_uint_country_code(input logic [1:0][DATA_BUS_BIT_WIDTH - 1:0] buff);
            int unsigned country_code = {{(SIZEOF_UINT - DATA_BUS_BIT_WIDTH){1'b0}}, buff[1]} << DATA_BUS_BIT_WIDTH;
            country_code += {{(SIZEOF_UINT - DATA_BUS_BIT_WIDTH){1'b0}}, buff[0]};
        endfunction
        
        static function logic process_data_swiss_format(input reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] buffer);
            int unsigned control_number = buffer % 97;
        endfunction
        
        static function logic process_data_polish_format(input reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] buffer);
        
        endfunction
    endclass: DataSniffer
    


endmodule