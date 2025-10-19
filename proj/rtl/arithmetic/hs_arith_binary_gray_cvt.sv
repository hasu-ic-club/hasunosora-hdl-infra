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
// FILE NAME: hs_arith_binary_gray_cvt.sv
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
// PURPOSE: Combinational binary-Gray converter (forward/reverse)
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// REVERSE             bool_e      TRUE means Gray to binary   BOOL_FALSE
//                                 FALSE means binary to Gray
// WIDTH               2-32        Data width                  8
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Combinational binary-Gray converter (forward/reverse)
module hs_arith_binary_gray_cvt
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter bool_e REVERSE = BOOL_FALSE,
    parameter int    WIDTH   = 8
)
(
    input  logic [WIDTH - 1:0] din,
    output logic [WIDTH - 1:0] dout
);

`GENERATE_START
if (REVERSE == BOOL_FALSE) begin : bin_gray_cvt
    assign dout = din ^ (din >> 1);
end : bin_gray_cvt
else begin : gray_bin_cvt
    genvar idx;
    
    logic [WIDTH - 1:0] cvt_buffer;
    
    assign cvt_buffer[WIDTH - 1] = din[WIDTH - 1];
    
    for (idx = WIDTH - 2; idx >= 0; idx--) begin : rev_cvt_loop
        assign cvt_buffer[idx] = cvt_buffer[idx + 1] ^ din[idx];
    end : rev_cvt_loop
    
    assign dout = cvt_buffer;
end : gray_bin_cvt
`GENERATE_END

endmodule : hs_arith_binary_gray_cvt