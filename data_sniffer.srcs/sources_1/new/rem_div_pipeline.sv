

module rem_div_pipeline
    (
        input
            wire clk,
            wire nreset,
            wire [15:0][7:0] input_buff,
        output
            reg [7:0] remainder
    );
    /* Local parameters */
    localparam INTERMEDIATE_RESULT_SIZE = $clog2(16 * 96**2);
    localparam INTERMEDIATE_RESULT_BYTE_COUNT = $ceil(INTERMEDIATE_RESULT_SIZE / 8);
    /* Internal signals and logic */
    byte unsigned loop_cnt;
    wire [15:0][15:0] remainder_stage_1;
    wire [INTERMEDIATE_RESULT_BYTE_COUNT - 1:0][7:0] remainder_stage_2;
    wire [INTERMEDIATE_RESULT_BYTE_COUNT - 1:0][15:0] remainder_stage_3;
    reg [15:0] multiple_of_97_lut [21:0];
    wire [1:0][7:0] final_stage;
    wire [7:0] result;
    reg [7:0] result_seq;
    
    generate
        genvar byte_count, reduced_byte_count, mul_count;
        for (byte_count = 0; byte_count < 16; byte_count++) begin
            rem_div_element #(.BYTE_POSITION(byte_count))
                byte_rem_divider_stage_1(
                    .clk(clk),
                    .nreset(nreset),
                    .single_byte(input_buff[byte_count]),
                    .remainder(remainder_stage_1[byte_count]));
        end
        for (reduced_byte_count = 0; reduced_byte_count < INTERMEDIATE_RESULT_BYTE_COUNT; reduced_byte_count++) begin
            rem_div_element #(.BYTE_POSITION(reduced_byte_count)) byte_rem_divider_stage_2(
                .clk(clk),
                .nreset(nreset),
                .single_byte(remainder_stage_2[reduced_byte_count]),
                .remainder(remainder_stage_3[reduced_byte_count]));
        end
        
    endgenerate 
    
    assign remainder_stage_2 = remainder_stage_1[0] +
                               remainder_stage_1[1] +
                               remainder_stage_1[2] +
                               remainder_stage_1[3] +
                               remainder_stage_1[4] +
                               remainder_stage_1[5] +
                               remainder_stage_1[6] +
                               remainder_stage_1[7] +
                               remainder_stage_1[8] +
                               remainder_stage_1[9] +
                               remainder_stage_1[10] +
                               remainder_stage_1[11] +
                               remainder_stage_1[12] +
                               remainder_stage_1[13] +
                               remainder_stage_1[14] +
                               remainder_stage_1[15];
    assign final_stage = remainder_stage_3[0] +
                         remainder_stage_3[1] +
                         remainder_stage_3[2];
    
    initial begin
        automatic shortint unsigned prev_multiple = 0;
        automatic shortint unsigned idx = 2;
        multiple_of_97_lut[0] = 0;
        multiple_of_97_lut[1] = 'd194;
        for (int i = 0; i < 62*97; i++) begin
            if ((i % 97 == 0) && (i - prev_multiple > 255)) begin
                multiple_of_97_lut[idx] = i;
                idx += 1; 
            end
        end
    end
    
    always @(posedge clk) begin
        if (1'b0 == nreset)
            result_seq <= 0;
        else begin
            /* Loop smaller than array by 1 index */
            for (loop_cnt=0; loop_cnt < 21; loop_cnt++) begin
                if ((multiple_of_97_lut[loop_cnt + 1] > final_stage) && (multiple_of_97_lut[loop_cnt] <= final_stage))
                    result_seq <= final_stage - multiple_of_97_lut[loop_cnt]; 
            end
        end
    end
    
endmodule 