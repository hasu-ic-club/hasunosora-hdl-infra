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
// FILE NAME: hs_unit_dff_noreset.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/26     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Paramaterized D-flip flop register (DFF) without Reset
//   This module has generic type in/out, that can compatible with
// different data types.
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE       DESCRIPTION            DEFAULT VALUE
// DATA_TYPE         Type        The I/O data type      logic
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Paramaterized D-flip flop register (DFF) without Reset
module hs_unit_dff_noreset
#(
    parameter type DATA_TYPE = logic
)
(
    input  logic     clk,
    input  DATA_TYPE din,
    output DATA_TYPE dout
);

DATA_TYPE dff;

always_ff @(posedge clk) begin : dff_reg
    dff <= din;
end : dff_reg

assign dout = dff;

endmodule : hs_unit_dff_noreset