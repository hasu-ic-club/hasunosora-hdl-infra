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
// FILE NAME: hs_arith_multi_in_uminimize.sv
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
// PURPOSE: Get the value and index of minimum (unsigned) 
//         item from multiple inputs
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Get the value and index of minimum (unsigned) item from multiple inputs
module hs_arith_multi_in_uminimize
    import hs_ifr_misc_typedefs_pkg::bool_e;
#(
    parameter  int    DATA_WIDTH      = 32,
    parameter  int    INPUT_NUM       = 4,
    parameter  bool_e ENABLE_AUX_PATH = hs_ifr_misc_typedefs_pkg::BOOL_TRUE,
    parameter  type   AUX_DATA_TYPE   = logic,

    `LP_MODULE int    INDEX_WIDTH     = $clog2(INPUT_NUM)
)
(
    input  logic         [DATA_WIDTH - 1:0]  din              [INPUT_NUM],
    input  AUX_DATA_TYPE                     aux_din          [INPUT_NUM],
    input  logic                             valid            [INPUT_NUM],

    output logic         [DATA_WIDTH - 1:0]  minimal_value,
    output AUX_DATA_TYPE                     minimal_aux_data,
    output logic         [INDEX_WIDTH - 1:0] minimal_index,
    output logic                             minimal_valid
);


genvar                                  lvl, index;

typedef struct packed
{
    AUX_DATA_TYPE             aux_data;
    logic [INDEX_WIDTH - 1:0] idx;
} min_aux_bundle_s;


localparam       int                    MIN2_LEVEL                                  = $clog2(INPUT_NUM);

logic                [DATA_WIDTH - 1:0] result          [MIN2_LEVEL + 1][INPUT_NUM];
min_aux_bundle_s                        result_aux      [MIN2_LEVEL + 1][INPUT_NUM];
logic                                   result_valid    [MIN2_LEVEL + 1][INPUT_NUM];

`GENERATE_START
for (index = 0; index < INPUT_NUM; index++) begin : min_inputs
    assign result[0][index]              = din[index];
    assign result_aux[0][index].idx      = INDEX_WIDTH'(index);
    assign result_aux[0][index].aux_data = aux_din[index];
    assign result_valid[0][index]        = valid[index];
end : min_inputs
`GENERATE_END

`GENERATE_START
for (lvl = 0; lvl < MIN2_LEVEL; lvl++) begin : min_levels
    for (index = 0; index < INPUT_NUM / (2 ** (lvl + 1)); index++) begin : min_level

        // Use the dual-input minimizer to get the minimal value
        // The auxiliary path is used for passing the index and user's auxiliary data

        hs_arith_dual_in_uminimize #(.DATA_WIDTH     (DATA_WIDTH      ),
            .ENABLE_AUX_PATH(hs_ifr_misc_typedefs_pkg::BOOL_TRUE          ),
            .AUX_DATA_TYPE  (min_aux_bundle_s)
        )
        d_in_min_inst
        (
            .din0            (result[lvl][index]                                     ),
            .din1            (result[lvl][index + INPUT_NUM / (2 ** (lvl + 1))]      ),
            .din0_valid      (result_valid[lvl][index]                               ),
            .din1_valid      (result_valid[lvl][index + INPUT_NUM / (2 ** (lvl + 1))]),
            .aux_din0        (result_aux[lvl][index]                                 ),
            .aux_din1        (result_aux[lvl][index + INPUT_NUM / (2 ** (lvl + 1))]  ),
            .minimal_value   (result[lvl + 1][index]                                 ),
            .minimal_aux_data(result_aux[lvl + 1][index]                             ),
            .minimal_index   (                                                       ),
            .minimal_valid   (result_valid[lvl + 1][index]                           )
        );
    end : min_level
end : min_levels
`GENERATE_END

assign minimal_index    = result_aux[MIN2_LEVEL][0].idx;
assign minimal_value    = result[MIN2_LEVEL][0];
assign minimal_valid    = result_valid[MIN2_LEVEL][0];

`GENERATE_START
if (ENABLE_AUX_PATH == hs_ifr_misc_typedefs_pkg::BOOL_TRUE) begin : enable_aux_path
    assign minimal_aux_data = result_aux[MIN2_LEVEL][0].aux_data;
end : enable_aux_path
else begin : disable_aux_path
    assign minimal_aux_data = '0;
end : disable_aux_path
`GENERATE_END

endmodule : hs_arith_multi_in_uminimize