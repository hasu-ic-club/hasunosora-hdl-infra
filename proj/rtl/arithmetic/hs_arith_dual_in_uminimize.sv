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
// FILE NAME: hs_arith_dual_in_uminimize.sv
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
// PURPOSE: Get the value and index of minimum (unsigned) item from 2 inputs
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE          DESCRIPTION                  DEFAULT VALUE
// DATA_WIDTH          1-128          Bit width of data to compare 32
// ENABLE_AUX_PATH     bool_e         Enable/disable auxiliary     hs_ifr_misc_typedefs_pkg::BOOL_TRUE
//                                    data input
// AUX_DATA_TYPE       type           Data type in auxiliary path  logic
//                                    (When disabled, set to 'logic')
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Get the value and index of minimum (unsigned) item from 2 inputs
module hs_arith_dual_in_uminimize
    import hs_ifr_misc_typedefs_pkg::bool_e;
#(
    parameter int    DATA_WIDTH      = 32,
    parameter bool_e ENABLE_AUX_PATH = hs_ifr_misc_typedefs_pkg::BOOL_TRUE,
    parameter type   AUX_DATA_TYPE   = logic
)
(
    // Data input
    input  logic         [DATA_WIDTH - 1:0] din0,
    input  logic         [DATA_WIDTH - 1:0] din1,

    // Data valid flag
    input  logic                            din0_valid,
    input  logic                            din1_valid,

    // Auxiliary data input
    input  AUX_DATA_TYPE                    aux_din0,
    input  AUX_DATA_TYPE                    aux_din1,

    // Minimal output
    output logic         [DATA_WIDTH - 1:0] minimal_value,
    output AUX_DATA_TYPE                    minimal_aux_data,
    output logic                            minimal_index,
    output logic                            minimal_valid
);

logic [1:0] valid_packed;
logic       comparator;
logic       sel;

assign valid_packed     = {din1_valid, din0_valid};
assign minimal_valid    = |valid_packed;
assign comparator       = din1 < din0;

always_comb begin : minimize
    unique case (valid_packed)
        2'b00: sel = 1'd0;
        2'b01: sel = 1'd0;
        2'b10: sel = 1'd1;
        2'b11: sel = comparator;
    endcase
end : minimize

assign minimal_index    = sel;
assign minimal_value    = sel ? din1 : din0;

`GENERATE_START
if (ENABLE_AUX_PATH == hs_ifr_misc_typedefs_pkg::BOOL_TRUE) begin : enable_aux_path
assign minimal_aux_data = sel ? aux_din1 : aux_din0;
end : enable_aux_path
else begin : disable_aux_path
assign minimal_aux_data = '0;
end : disable_aux_path
`GENERATE_END

endmodule : hs_arith_dual_in_uminimize