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
    

    /* Typedefs */
    typedef logic [127:0] unsigned_triple_long_int;
    typedef enum logic[2:0] {
        RESULT_SWISS_CC_BUT_NO_MATCH,
        RESULT_SWISS_CC_MATCH,
        RESULT_POLISH_CC_BUT_NO_MATCH,
        RESULT_POLISH_CC_MATCH,
        RESULT_CC_POSSIBLE_BUT_NO_MATCH,
        RESULT_CC_NOT_POSSIBLE
    } data_investigation_result_type;
    
    /* Internal signals */
    reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] local_fifo;
    
    
    class DataSniffer #(int DATA_BUS_BIT_WIDTH = 'x,
                        int FIFO_BYTE_LENGTH = 'x,
                        type iban_num_type = unsigned_triple_long_int);
        /* Local parameters with all necessary constants */
        localparam SIZEOF_UINT = $bits(int unsigned);
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
        local function void convert_string_stream_to_binary(input reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] buff);
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
        local function void convert_binary_stream_to_number_swiss();
            /* TODO: Check if implicit assign like that is acceptable */
            iban_as_num = 0;
            for (int segment=0; segment<SWISS_FORMAT_IBAN_LENGTH; ++segment) begin
                iban_as_num += iban_num_type'(this.swiss_buffer[segment]) * ('d10 ** segment);
            end
        endfunction

        /**
        * This function converts a buffer of binary values to a number, from polish format.
        */
        local function void convert_binary_stream_to_number_polish();
            /* TODO: Check if implicit assign like that is acceptable */
            iban_as_num = 0;
            for (int segment=0; segment<POLISH_FORMAT_IBAN_LENGTH; ++segment) begin
                iban_as_num += iban_num_type'(this.polish_buffer[segment]) * ('d10 ** segment);
            end
        endfunction

        /**
        * Function for calculating remainder from division of potentially really large numbers.
        */
        local function int unsigned calculate_remainder(input iban_num_type divisor);
            iban_num_type remainder = this.iban_as_num;
            while (remainder >= divisor) begin
                remainder -= divisor;
            end
            return unsigned'(int'(remainder));
        endfunction
        
        local function logic check_if_country_code_correct(input int unsigned country_code);
            if ((MAX_POSSIBLE_COUNTRY_CODE_VAL < country_code) || (MIN_POSSIBLE_COUNTRY_CODE_VAL > country_code)) begin
                `SIM_LOG_ERROR({"Unknown country code: ", string'(country_code)});
                return 1'b0;
            end
            else begin
                `SIM_LOG_INFO({"Country code in valid range: ", string'(country_code)});
                 return 1'b1;
            end
        endfunction
            
        local function logic [2:0] try_find_pattern(input int unsigned country_code);
            case (country_code)
                'd1217: return {1'b0, 1'b0, process_data_swiss_format()};
                'd2521: return {1'b0, 1'b1, process_data_polish_format()};
                default: return {3'b1};
            endcase
        endfunction
        
        /* Function for calculating country code directly from buffer */
        local function int unsigned convert_raw_data_to_uint_country_code_or_checksum(input reg [1:0][DATA_BUS_BIT_WIDTH - 1:0] buff);
            int unsigned country_code_or_checksum = {{(SIZEOF_UINT - DATA_BUS_BIT_WIDTH){1'b0}}, buff[0]};
            country_code_or_checksum += {{(SIZEOF_UINT - DATA_BUS_BIT_WIDTH){1'b0}}, buff[1]} * 'd10;
            return country_code_or_checksum;
        endfunction

        /* Function for rotating left the swiss buffer by a fixed amount required by the standard */
        local function reg [SWISS_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] rotate_left_swiss();
            reg [SWISS_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] temp_buff;
            temp_buff[SWISS_FORMAT_IBAN_LENGTH - 1: SWISS_FORMAT_IBAN_LENGTH - 16] = this.swiss_buffer[SWISS_FORMAT_IBAN_LENGTH - 5:0];
            temp_buff[SWISS_FORMAT_IBAN_LENGTH - 5:0] = this.swiss_buffer[SWISS_FORMAT_IBAN_LENGTH - 1:SWISS_FORMAT_IBAN_LENGTH - 4];
            return temp_buff;
        endfunction

        local function reg [POLISH_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] rotate_left_polish();
            reg [POLISH_FORMAT_IBAN_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] temp_buff;
            temp_buff[POLISH_FORMAT_IBAN_LENGTH - 1: POLISH_FORMAT_IBAN_LENGTH - 16] = this.polish_buffer[POLISH_FORMAT_IBAN_LENGTH - 5:0];
            temp_buff[POLISH_FORMAT_IBAN_LENGTH - 5:0] = this.swiss_buffer[POLISH_FORMAT_IBAN_LENGTH - 1:POLISH_FORMAT_IBAN_LENGTH - 4];
            return temp_buff;
        endfunction
        
        local function logic process_data_swiss_format();
            int unsigned remainder;
            int unsigned checksum_calculated;
            /* First, save the potential control number for later comparison and zero-out
            * the fields in buffer in which the control number resides.
            */
            reg [1:0][DATA_BUS_BIT_WIDTH - 1:0] control_number = this.swiss_buffer[SWISS_FORMAT_IBAN_LENGTH-3:SWISS_FORMAT_IBAN_LENGTH-4];
            this.swiss_buffer[SWISS_FORMAT_IBAN_LENGTH-3:SWISS_FORMAT_IBAN_LENGTH-4] = 0; /* TODO: Check if implicit assignment is sufficient */
            /* Rotate the buffer accordingly */
            this.swiss_buffer = this.rotate_left_swiss();
            /* Convert binary format to an actual number */
            this.convert_binary_stream_to_number_swiss();
            /* Calculate remainder from the division */
            remainder = this.calculate_remainder(iban_num_type'(SWISS_CHECKSUM_DIVIDER));
            /* Calculate the checksum */
            checksum_calculated = SWISS_CHECKSUM_DIVIDER + 1 - remainder;
            /* Compare to the received checksum */
            if (this.convert_raw_data_to_uint_country_code_or_checksum(control_number) != checksum_calculated)
                return 0;
            else return 1;
        endfunction
        
        local function logic process_data_polish_format();
            int unsigned remainder;
            /* In Polish version, according to the information found, we can determine if the control
            * number is correct without saving it, only by performing certain operations on the data.
            */
            /* First, rotate the buffer */
            this.polish_buffer = this.rotate_left_polish();
            /* Convert binary format to an actual number */
            this.convert_binary_stream_to_number_polish();
            /* Calculate remainder from the division */
            remainder = this.calculate_remainder(iban_num_type'(POLISH_CHECKSUM_DIVIDER));
            /* According to information found, if remainder == 1, then checksum is correct */
            if('d1 != remainder)
                return 0;
            else return 1;
        endfunction

        /* Main function in this class - encapsulates all the processing */
        function data_investigation_result_type main_function(input reg [FIFO_BYTE_LENGTH - 1:0][DATA_BUS_BIT_WIDTH - 1:0] buff);
            int unsigned country_code;
            logic [2:0] processing_result;
            /* First, convert the data and write it to internal buffer */
            this.convert_string_stream_to_binary(buff);
            /* Crop and rewrite converted data into both formats processing buffers */
            this.swiss_buffer = this.priv_fifo_buff[FIFO_BYTE_LENGTH - 1:FIFO_BYTE_LENGTH - SWISS_FORMAT_IBAN_LENGTH];
            this.polish_buffer = this.priv_fifo_buff[FIFO_BYTE_LENGTH - 1:FIFO_BYTE_LENGTH - POLISH_FORMAT_IBAN_LENGTH];
            /* Calculate and check the country code */
            country_code = this.convert_raw_data_to_uint_country_code_or_checksum(this.priv_fifo_buff[FIFO_BYTE_LENGTH - 1:FIFO_BYTE_LENGTH - 2]);
            if (1'b0 == this.check_if_country_code_correct(country_code))
                return RESULT_CC_NOT_POSSIBLE;
            /* If country code possible, try to process it */
            processing_result = this.try_find_pattern(country_code);
            case(processing_result)
            3'b000: return RESULT_SWISS_CC_BUT_NO_MATCH;
            3'b001: return RESULT_SWISS_CC_MATCH;
            3'b010: return RESULT_POLISH_CC_BUT_NO_MATCH;
            3'b011: return RESULT_POLISH_CC_MATCH;
            3'b111: return RESULT_CC_POSSIBLE_BUT_NO_MATCH;
            default: `SIM_LOG_ERROR("Impossible state entered!");
            endcase
            return RESULT_CC_NOT_POSSIBLE;
        endfunction
    endclass: DataSniffer
    


endmodule