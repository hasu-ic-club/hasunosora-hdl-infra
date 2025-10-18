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
// FILE NAME: hs_cdc_syncer.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/25     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Multi-stage asynchronous synchronizer (1-bit)
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// SYNC_STAGE          2-32        Series stage count of       2
//                                 the synchronizer
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Multi-stage asynchronous synchronizer (1-bit)
module hs_cdc_syncer
#(
    parameter int SYNC_STAGE = 2
)
(
    input  logic clk,
    input  logic aresetn,
    input  logic din,
    output logic dout
);

genvar idx;

`ASYNC_REG_HINT logic [SYNC_STAGE - 1:0] sync_ff;

`GENERATE_START
for (idx = 0; idx < SYNC_STAGE; idx++) begin : multi_stage_sync
    if (idx == 0) begin : first_stage
        always_ff @(posedge clk, negedge aresetn) begin
            if (!aresetn) sync_ff[idx] <= '0;
            else          sync_ff[idx] <= din;
        end
    end : first_stage
    else begin : other_stage
        always_ff @(posedge clk, negedge aresetn) begin
            if (!aresetn) sync_ff[idx] <= '0;
            else          sync_ff[idx] <= sync_ff[idx - 1];
        end
    end : other_stage
end : multi_stage_sync
`GENERATE_END

assign dout = sync_ff[SYNC_STAGE - 1];

endmodule : hs_cdc_syncer