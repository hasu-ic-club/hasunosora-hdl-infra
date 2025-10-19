//+FHDR--------------------------------------------------------------------
// Copyright (C) 2025 Hasunosora IC Design Club
// MIT License
// Permission is hereby granted, free of charge, to any person obtaining a 
// copy of this design and associated documentation files (the “Design”), 
// to deal in the Design without restriction, including without limitation 
// the rights to use, copy, modify, merge, publish, distribute, sublicense, 
// and/or sell copies of the Design, and to permit persons to whom the 
// Design is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included 
// in all copies or substantial portions of the Design.
//
// THE DESIGN IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, 
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF 
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. 
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, 
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, 
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE 
// DESIGN OR THE USE OR OTHER DEALINGS IN THE DESIGN.
//-------------------------------------------------------------------------
// FILE NAME: rtl/arithmetic/hs_arith_multi_in_uadder_pipe.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/9      First Edition
//-------------------------------------------------------------------------
// PURPOSE: Pipelined multiple input unsigned adder
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME        RANGE           DESCRIPTION                 DEFAULT VALUE
// DATA_WIDTH            1-4096          Bit width of data           1
// INPUT_NUM             2-128           Number of input ports       16
// PIPE_INSERT_INTERVAL  1-16            Pipeling register slice     1
//                                       insert interval
// INPUT_REGISTER        bool_e          Enable input register slice hs_ifr_misc_typedefs_pkg::BOOL_FALSE
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Pipelined multiple input unsigned adder
module hs_arith_multi_in_uadder_pipe
    import hs_ifr_misc_typedefs_pkg::bool_e;
#(
    parameter  int    DATA_WIDTH           = 8,
    parameter  int    INPUT_NUM            = 16,
    parameter  int    PIPE_INSERT_INTERVAL = 1,
    parameter  bool_e EN_INPUT_REG         = hs_ifr_misc_typedefs_pkg::BOOL_FALSE,
    `LP_MODULE int    EACH_INPUT_MAX       = (2 ** (DATA_WIDTH) - 1),
    `LP_MODULE int    OUTPUT_MAX           = INPUT_NUM * EACH_INPUT_MAX,
    `LP_MODULE int    OUTPUT_WIDTH         = $clog2(OUTPUT_MAX + 1)
)
(
    // Clock & reset
    input  logic                      clk,
    input  logic                      aresetn,

    // Clock enable
    input  logic                      ce,

    // Data I/O
    input  logic [DATA_WIDTH - 1:0]   din     [INPUT_NUM],
    output logic [OUTPUT_WIDTH - 1:0] dout
);

localparam int                      ADD2_LEVEL                                          = $clog2(INPUT_NUM);
localparam int                      REG_SLICE_LEVEL                                     = ADD2_LEVEL / PIPE_INSERT_INTERVAL + (EN_INPUT_REG == hs_ifr_misc_typedefs_pkg::BOOL_TRUE ? 1 : 0);
localparam int                      INPUT_NUM_UPCEIL                                    = 2 ** ADD2_LEVEL;
localparam int                      CE_TAP_LENGTH                                       = REG_SLICE_LEVEL == 0 ? 1 : REG_SLICE_LEVEL;

genvar                              lvl, index;

logic                               ce_tap           [CE_TAP_LENGTH];
logic          [OUTPUT_WIDTH - 1:0] add2_result      [ADD2_LEVEL + 1][INPUT_NUM_UPCEIL];


// Clock enable chain
`GENERATE_START
if (REG_SLICE_LEVEL == 0) begin : no_ce_needed
    assign ce_tap[0] = 1'b0;
end : no_ce_needed
else if (REG_SLICE_LEVEL == 1) begin : no_ce_chain_needed
    assign ce_tap[0] = ce;
end : no_ce_chain_needed
else begin : ce_chain_config
    hs_dpath_ce_chain
    #(
        .LATENCY(REG_SLICE_LEVEL - 1)
    )
    ce_adder_inst
    (
        .clk    (clk    ),
        .aresetn(aresetn),
        .ce     (ce     ),
        .ce_out (ce_tap )
    );
end : ce_chain_config
`GENERATE_END


// Input register
`GENERATE_START
for (index = 0; index < INPUT_NUM_UPCEIL; index++) begin : adder_inputs
    if (index < INPUT_NUM) begin : adder_input_in_range
        if (EN_INPUT_REG == hs_ifr_misc_typedefs_pkg::BOOL_TRUE) begin : adder_input_regslice
            always_ff @(posedge clk) begin
                if (ce_tap[0]) add2_result[0][index] <= OUTPUT_WIDTH'(din[index]);
            end
        end : adder_input_regslice
        else begin : adder_input_noreg
            assign add2_result[0][index] = OUTPUT_WIDTH'(din[index]);
        end : adder_input_noreg
    end : adder_input_in_range
    else begin : adder_input_padding
        assign add2_result[0][index] = 'd0;
    end : adder_input_padding
end : adder_inputs

// Adder pipeline
for (lvl = 0; lvl < ADD2_LEVEL; lvl++) begin : adder_levels
    if ((lvl % PIPE_INSERT_INTERVAL) == (PIPE_INSERT_INTERVAL - 1)) begin : adder_insert_pipe
        for (index = 0; index < INPUT_NUM_UPCEIL / (2 ** (lvl + 1)); index++) begin : adder_level_pipe
            always_ff @(posedge clk) begin
                if ((EN_INPUT_REG == hs_ifr_misc_typedefs_pkg::BOOL_TRUE) ? ce_tap[(lvl / PIPE_INSERT_INTERVAL) + 1] : ce_tap[(lvl / PIPE_INSERT_INTERVAL)]) begin
                    // When we enabled the input register, the CE of the first adder level must be
                    // shift by one clock cycle to ensure the correct result.
                    add2_result[lvl + 1][index]           <= add2_result[lvl][index] + add2_result[lvl][index + INPUT_NUM_UPCEIL / (2 ** (lvl + 1))];
                end
            end
        end : adder_level_pipe
    end : adder_insert_pipe
    else begin : adder_no_insert_pipe
        for (index = 0; index < INPUT_NUM_UPCEIL / (2 ** (lvl + 1)); index++) begin : adder_level_no_pipe
            assign add2_result[lvl + 1][index] = add2_result[lvl][index] + add2_result[lvl][index + INPUT_NUM_UPCEIL / (2 ** (lvl + 1))];
        end : adder_level_no_pipe
    end : adder_no_insert_pipe
end : adder_levels
`GENERATE_END

assign dout = add2_result[ADD2_LEVEL][0];


endmodule : hs_arith_multi_in_uadder_pipe