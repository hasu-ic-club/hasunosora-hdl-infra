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
// FILE NAME: hs_unit_dff_ce.sv
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
//  Paramaterized D-flip flop register (DFF) w/ Clock Enable
//  This module has generic type in/out, that can compatible with
// different data types.
//-----------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE              DESCRIPTION            DEFAULT VALUE
// DATA_TYPE         Type               The I/O data type      logic
// RESET_VALUE       Range of DATA_TYPE Value when DFF reset   1'b0
//-FHDR------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Paramaterized D-flip flop register (DFF) w/ Clock Enable
module hs_unit_dff_ce
#(
    parameter type      DATA_TYPE   = logic,
    parameter DATA_TYPE RESET_VALUE = 1'b0
)
(
    // Clock & reset
    input  logic     clk,
    input  logic     aresetn,

    // Clock enable
    input  logic     ce,

    // Input data
    input  DATA_TYPE din,

    // Output data
    output DATA_TYPE dout
);

DATA_TYPE dff;

always_ff @(posedge clk, negedge aresetn) begin : dff_reg
    if (!aresetn) dff <= RESET_VALUE;
    else if (ce)  dff <= din;
end : dff_reg

assign dout = dff;

endmodule : hs_unit_dff_ce
