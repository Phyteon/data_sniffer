

module data_sniffer #(
    int DATA_BUS_BIT_WIDTH = 'x
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
    
    class DataSnifferBehavModel #(int DATA_BUS_BIT_WIDTH = 'x);
        local logic [DATA_BUS_BIT_WIDTH - 1:0] recognised_data;
        local logic [7:0] recognised_data_type;
        
        /**
        * Function for calculating control number out of the potential bank account number.
        * IMPORTANT! Control number calculation is done according to Swiss regulations,
        * regulations in Poland may require different method! Please check ISO 7064.
        *
        * In Switzerland, the control number is calcultated by division with remainder of
        * the bank account number, by 97. That remainder is then subtracted from 97 + 1,
        * and the result is the control number.
        */
        function int unsigned calculate_control_number(input int unsigned account_number);
            int unsigned div_remainder = account_number % 97;
            int unsigned control_number = 98 - div_remainder;
            return control_number;
        endfunction
        
        /**
        * Checks if the country code provided is valid. Input is assumed to be two
        * ASCII characters in one number, where the left letter is the older byte
        * and the right letter is the younger byte.
        */
        function logic check_if_country_code_correct(input int unsigned country_code);
            
        endfunction
    endclass



endmodule