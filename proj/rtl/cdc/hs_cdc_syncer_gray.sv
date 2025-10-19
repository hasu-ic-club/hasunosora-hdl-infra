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
// FILE NAME: hs_cdc_syncer_gray.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/27     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Gray-encoded multi-bit synchronizer
//   NOTE: It is danguous that use this module to pass non-counter multi-bit
//         signal. This module module should be used only for the value of
//         add-1 counters to cross domain.
//         If the signal is randomly changed or not changed only +1/-1 one
//         clock, please consider to use FIFO or 2-phase handshake module
//         for them.
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// SYNC_STAGE          2-32        Series stage count of the   2
//                                 synchronizer
// WIDTH               1-32        Width of data               8
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Gray-encoded multi-bit synchronizer
module hs_cdc_syncer_gray
import hs_ifr_misc_typedefs_pkg::*;
#(

    parameter int SYNC_STAGE = 2,
    parameter int WIDTH      = 8
)
(
    input  logic               clk,
    input  logic               aresetn,
    input  logic [WIDTH - 1:0] din,
    output logic [WIDTH - 1:0] dout
);

logic [WIDTH - 1:0] gray;
logic [WIDTH - 1:0] gray_synced;

hs_arith_binary_gray_cvt #(
    .REVERSE(BOOL_FALSE),
    .WIDTH  (WIDTH     )
)
bin2gray_inst
(
    .din (din ),
    .dout(gray)
);

hs_cdc_syncer_mb #(
    .SYNC_STAGE(SYNC_STAGE),
    .WIDTH     (WIDTH     )
)
cdc_syncer_inst
(
    .clk    (clk        ),
    .aresetn(aresetn    ),
    .din    (gray       ),
    .dout   (gray_synced)
);


hs_arith_binary_gray_cvt #(
    .REVERSE(BOOL_TRUE),
    .WIDTH  (WIDTH    )
)
gray2bin_inst
(
    .din (gray_synced),
    .dout(dout       )
);

endmodule : hs_cdc_syncer_gray