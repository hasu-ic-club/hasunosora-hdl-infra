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
// FILE NAME: hs_cdc_syncer_mb.sv
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
// PURPOSE: Multi-bit multi-stage asynchronous synchronizer
//   NOTE: It is danguous that use this module to pass ANY multi-bit signal
//         directly. This module should be used only for Gray encoded signals
//         in asynchronous FIFO or asynchronous counters.
//         Please consider to use FIFO or 2-phase handshake module for
//         any other signals who need to cross clock domain
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

// Multi-bit multi-stage asynchronous synchronizer
module hs_cdc_syncer_mb
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

genvar idx;

`GENERATE_START
for (idx = 0; idx < WIDTH; idx++) begin : cdc_vector
    hs_cdc_syncer #(
        .SYNC_STAGE(SYNC_STAGE)
    )
    cdc_inst
    (
        .clk    (clk      ),
        .aresetn(aresetn  ),
        .din    (din[idx] ),
        .dout   (dout[idx])
    );
end : cdc_vector
`GENERATE_END

endmodule : hs_cdc_syncer_mb