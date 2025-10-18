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
// FILE NAME: hs_arith_multi_in_uadder.sv
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
// PURPOSE: Multiple input unsigned adder
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// DATA_WIDTH          1-4096      Bit width of data              1
// INPUT_NUM           2-128       Number of input ports          16
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Multiple input unsigned adder
module hs_arith_multi_in_uadder
#(
    parameter  int DATA_WIDTH     = 1,
    parameter  int INPUT_NUM      = 16,
    `LP_MODULE int EACH_INPUT_MAX = (2 ** (DATA_WIDTH) - 1),
    `LP_MODULE int OUTPUT_MAX     = INPUT_NUM * EACH_INPUT_MAX,
    `LP_MODULE int OUTPUT_WIDTH   = $clog2(OUTPUT_MAX + 1)
)
(
    input  logic [DATA_WIDTH - 1:0]   din  [INPUT_NUM],
    output logic [OUTPUT_WIDTH - 1:0] dout
);


localparam int                      ADD2_LEVEL                              = $clog2(INPUT_NUM);

genvar                              lvl, index;

logic          [OUTPUT_WIDTH - 1:0] add2_result [ADD2_LEVEL + 1][INPUT_NUM];

`GENERATE_START
for (index = 0; index < INPUT_NUM; index++) begin : adder_inputs
    assign add2_result[0][index] = OUTPUT_WIDTH'(din[index]);
end : adder_inputs

for (lvl = 0; lvl < ADD2_LEVEL; lvl++) begin : adder_levels
    for (index = 0; index < INPUT_NUM / (2 ** (lvl + 1)); index++) begin : adder_level
        assign add2_result[lvl + 1][index] = add2_result[lvl][index] + add2_result[lvl][index + INPUT_NUM / (2 ** (lvl + 1))];
    end : adder_level
end : adder_levels
`GENERATE_END

assign dout = add2_result[ADD2_LEVEL][0];

endmodule : hs_arith_multi_in_uadder