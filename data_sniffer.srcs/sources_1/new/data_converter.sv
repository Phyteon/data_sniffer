

module data_converter
    (
        input
            wire clk,
            wire nreset,
            wire [7:0] data_chunk,
        output wire [7:0] data_processed
    );
    /**
     * This module is responsible for converting one byte of data from data FIFO
     * according to IBAN conversion table. If incoming symbol is not uppercase letter
     * or digit, the output value is 8'hFF.
     */
    /* Local parameters */
    localparam byte unsigned iban_letter_lut [0:25] = {'d10, 'd11, 'd12, 'd13, 'd14, 'd15, 'd16, 'd17,
                                                       'd18, 'd19, 'd20, 'd21, 'd22, 'd23, 'd24, 'd25,
                                                       'd26, 'd27, 'd28, 'd29, 'd30, 'd31, 'd32, 'd33,
                                                       'd34, 'd35};
    localparam byte unsigned ASCII_CODE_FOR_DIGIT_ZERO = 'd48;
    localparam byte unsigned ASCII_CODE_FOR_DIGIT_NINE = 'd57;
    localparam byte unsigned ASCII_CODE_FOR_CAPITAL_LETTER_A = 'd65;
    localparam byte unsigned ASCII_CODE_FOR_CAPITAL_LETTER_Z = 'd90;
    /* Internal signals */
    reg [7:0] data_processed_s;
    wire data_is_uppercase_letter;
    wire data_is_digit;
    
    /* Internal logic */
    assign data_is_uppercase_letter = (ASCII_CODE_FOR_CAPITAL_LETTER_A <= data_chunk) ?
                                      ((ASCII_CODE_FOR_CAPITAL_LETTER_Z >= data_chunk) ?
                                      1'b1 : 1'b0) : 1'b0;
    
    assign data_is_digit = (ASCII_CODE_FOR_DIGIT_ZERO <= data_chunk) ?
                           ((ASCII_CODE_FOR_DIGIT_NINE >= data_chunk) ?
                           1'b1 : 1'b0) : 1'b0;
    
    always @(posedge clk or negedge nreset) begin
        if (1'b0 == nreset)
            data_processed_s <= 8'b0;
        else begin
            if (1'b1 == data_is_uppercase_letter)
                data_processed_s <= iban_letter_lut[data_chunk - ASCII_CODE_FOR_CAPITAL_LETTER_A];
            else if (1'b1 == data_is_digit)
                data_processed_s <= data_chunk - ASCII_CODE_FOR_DIGIT_ZERO;
            else
                data_processed_s <= 8'hFF;
        end
    end
    
    assign data_processed = data_processed_s;
    
    /* Properties and assertions */
    
    property pr__data_converter__status_signals_never_enabled_simultaneously;
        @(posedge clk) disable iff (!nreset)
            (data_is_uppercase_letter || data_is_digit)
                |->
            (1'b0 == (data_is_uppercase_letter & data_is_digit));
    endproperty
    
    as__data_converter__status_signals_never_enabled_simultaneously:
        assert property(pr__data_converter__status_signals_never_enabled_simultaneously)
            else
            $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
    
endmodule