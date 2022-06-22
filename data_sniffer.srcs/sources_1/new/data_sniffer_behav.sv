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
        reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] recognised_data_out, /* Recognised data out */
        reg [7:0] recognised_data_beginning_position_in_stream, /* Beginning position in the stream */
        reg [7:0] recognised_data_frame_count /* Span */
    );
    /* Local parameters */
    localparam SIZEOF_UINT = $bits(int unsigned);

    /* Typedefs */
    typedef logic [127:0] unsigned_triple_long_int;
    
    /* Internal signals */
    reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] local_fifo;
    
    
    class DataSniffer #(int DATA_BUS_BIT_WIDTH = 'x,
                        int FIFO_BYTE_LENGTH = 'x,
                        type iban_num_type = unsigned_triple_long_int);
        /* Local parameters with all necessary constants */
        localparam MAX_POSSIBLE_COUNTRY_CODE_VAL = 'd3535;
        localparam MIN_POSSIBLE_COUNTRY_CODE_VAL = 'd1010;
        localparam byte unsigned ASCII_CODE_FOR_DIGIT_ZERO = 'd48;
        localparam byte unsigned ASCII_CODE_FOR_DIGIT_NINE = 'd57;
        localparam byte unsigned ASCII_CODE_FOR_CAPITAL_LETTER_A = 'd65;
        localparam byte unsigned ASCII_CODE_FOR_CAPITAL_LETTER_Z = 'd90;
        localparam int unsigned SWISS_CHECKSUM_DIVIDER = 'd97;
        localparam int unsigned POLISH_CHECKSUM_DIVIDER = 'd97;
        localparam SWISS_FORMAT_IBAN_LENGTH = 'd21;
        localparam POLISH_FORMAT_IBAN_LENGTH = 'd28;
        localparam byte iban_letter_lut [0:24] = {'d10, 'd11, 'd12, 'd13, 'd14, 'd15, 'd16, 'd17,
                                                  'd18, 'd19, 'd20, 'd21, 'd22, 'd23, 'd24, 'd25,
                                                  'd26, 'd27, 'd28, 'd29, 'd30, 'd31, 'd32, 'd33,
                                                  'd34, 'd35};
        
        /* Internal variables and signals */
        local reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] priv_fifo_buff;
        local reg [SWISS_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] swiss_buffer;
        local reg [POLISH_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] polish_buffer;
        local iban_num_type iban_as_num;
        
        /**
        * This function converts ASCII string stream to binary data, but according to IBAN conversion table.
        * Numbers are converted normally, according to ASCII, but letters are converted using the IBAN conversion.
        */
        function void convert_string_stream_to_binary(input reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] buff);
            for (int segment=0; segment<FIFO_BYTE_LENGTH; ++segment) begin
                if ((ASCII_CODE_FOR_DIGIT_ZERO <= buff[segment]) && (ASCII_CODE_FOR_DIGIT_NINE >= buff[segment])) begin
                    /* Simply subtract the value for "0" to get the actual number */
                    this.priv_fifo_buff[segment] = buff[segment] - ASCII_CODE_FOR_DIGIT_ZERO;
                end else if ((ASCII_CODE_FOR_CAPITAL_LETTER_A <= buff[segment]) && (ASCII_CODE_FOR_CAPITAL_LETTER_Z >= buff[segment])) begin
                    /* If any capital letter is found, change it to a number according to LUT */
                    this.priv_fifo_buff[segment] = iban_letter_lut[buff[segment] - ASCII_CODE_FOR_CAPITAL_LETTER_A];
                end else begin
                    /* If another value is sent, write 255 */
                    this.priv_fifo_buff[segment] = 'hFF;
                    `SIM_LOG_INFO({"Irrelevant char: ", string'(buff[segment])});
                end
            end
        endfunction

        /**
        * This function converts a buffer of binary values to a number, from swiss format.
        */
        function void convert_binary_stream_to_number_swiss();
            /* TODO: Check if implicit assign like that is acceptable */
            iban_as_num = 0;
            for (int segment=0; segment<SWISS_FORMAT_IBAN_LENGTH; ++segment) begin
                iban_as_num += iban_num_type'(this.swiss_buffer[segment]) * ('d10 ** segment);
            end
        endfunction

        /**
        * This function converts a buffer of binary values to a number, from polish format.
        */
        function void convert_binary_stream_to_number_polish();
            /* TODO: Check if implicit assign like that is acceptable */
            iban_as_num = 0;
            for (int segment=0; segment<POLISH_FORMAT_IBAN_LENGTH; ++segment) begin
                iban_as_num += iban_num_type'(this.polish_buffer[segment]) * ('d10 ** segment);
            end
        endfunction

        /**
        * Function for calculating remainder from division of potentially really large numbers.
        */
        function int unsigned calculate_remainder(input iban_num_type divisor);
            iban_num_type remainder = this.iban_as_num;
            while (remainder >= divisor) begin
                remainder -= divisor;
            end
            return unsigned'(int'(remainder));
        endfunction
        
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
            
        static function int unsigned convert_raw_data_to_uint_country_code(input reg [1:0][DATA_BUS_BIT_WIDTH - 1:0] buff);
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