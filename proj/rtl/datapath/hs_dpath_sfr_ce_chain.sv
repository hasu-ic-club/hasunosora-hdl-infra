//+FHDR------------------------------------------------------------------
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
//-----------------------------------------------------------------------
// FILE NAME: hs_dpath_sfr_ce_chain.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-----------------------------------------------------------------------
// RELEASE VERSION:     0.1a0
// VERSION DESCRIPTION: Initial version
//-----------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/09       Initial version
//-----------------------------------------------------------------------
// PURPOSE:
//  Paramaterized shift register (SFR) w/ Clock Enable Chain
//  This module has generic type in/out, that can compatible with
// different data types.
//-----------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE         DESCRIPTION            DEFAULT VALUE
//-----------------------------------------------------------------------
// DATA_TYPE         Type          The I/O data type      logic
// RESET_VALUE       Range of T    Value when SFR reset   1'b0
// LATENCY           1:4294967295  The data latency from  1
//                                 input to output
//-FHDR------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Paramaterized shift register (SFR) w/ Clock Enable Chain
module hs_dpath_sfr_ce_chain
#(
    parameter type      DATA_TYPE   = logic,
    parameter DATA_TYPE RESET_VALUE = 1'b0,
    parameter int       LATENCY     = 1
)
(
    // Clock & reset
    input  logic     clk,
    input  logic     aresetn,

    // Clock enable
    input  logic     ce,     // Clock enable input
    output logic     ce_out, // Output from CE chain

    // Input data
    input  DATA_TYPE din,

    // Output data
    output DATA_TYPE dout
);

genvar         idx;
DATA_TYPE      sfr_reg[LATENCY];
logic          ce_reg [LATENCY];

// ce -> CE SFR
always_ff @(posedge clk, negedge aresetn) begin : ce_i_dff
    if (!aresetn) ce_reg[0] <= '0;
    else          ce_reg[0] <= din;
end : ce_i_dff

// din -> SFR
always_ff @(posedge clk, negedge aresetn) begin : sfr_in_dff
    if (!aresetn) sfr_reg[0] <= RESET_VALUE;
    else if (ce)  sfr_reg[0] <= din;
end : sfr_in_dff

// SFR level [n-1] -> [n]
`GENERATE_START
if (LATENCY > 1) begin : latency_gt_1
    for (idx = 1; idx < LATENCY; idx++) begin : sfr_ff
        always_ff @(posedge clk, negedge aresetn) begin : ce_dff
            if (!aresetn) ce_reg[idx] <= '0;
            else          ce_reg[idx] <= ce_reg[idx - 1];
        end : ce_dff

        always_ff @(posedge clk, negedge aresetn) begin : sfr_dff
            if (!aresetn)              sfr_reg[idx] <= RESET_VALUE;
            else if (ce_reg[idx -  1]) sfr_reg[idx] <= sfr_reg[idx - 1];
        end : sfr_dff
    end : sfr_ff
end : latency_gt_1
`GENERATE_END

// SFR -> dout
assign dout   = sfr_reg[LATENCY - 1];

// CE chain -> ce out
assign ce_out = ce_reg[LATENCY - 1];

endmodule : hs_dpath_sfr_ce_chain
