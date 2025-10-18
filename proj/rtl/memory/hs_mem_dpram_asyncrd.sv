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
// FILE NAME: hs_mem_dpram_asyncrd.sv
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
//  Dual-port RAM (1W/2R) w/ Latency = 0 (Asynchronous Read)
//-----------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE         DESCRIPTION            DEFAULT VALUE
//-----------------------------------------------------------------------
// DATA_TYPE         type          Item type in RAM       logic[7:0]
// DATA_DEPTH        1 - 1048576   RAM depth              16
//-FHDR------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Dual-port RAM (1W/2R) w/ Latency = 0 (Asynchronous Read)
module hs_mem_dpram_asyncrd
import hs_math_basic_pkg::ceil_to_nxt_pow2;
#(
    parameter  type DATA_TYPE  = logic[7:0],
    parameter  int  DATA_DEPTH = 16,

    `LP_MODULE int  ADDR_WIDTH = $clog2(DATA_DEPTH)
)
(
    // Clock (the RAM has not reset)
    input  logic                        clk,

    // RAM access port
    input  logic     [ADDR_WIDTH - 1:0] wr0addr,
    input  logic     [ADDR_WIDTH - 1:0] r1addr,
    input  DATA_TYPE                    wdata,
    output DATA_TYPE                    r0data,
    output DATA_TYPE                    r1data,
    input  logic                        wen
);


localparam int DATA_DEPTH_REAL                   = ceil_to_nxt_pow2(DATA_DEPTH);

DATA_TYPE      ram             [DATA_DEPTH_REAL];

always_ff @(posedge clk) begin : ram_access
    if (wen) begin
        ram[wr0addr] <= wdata;
    end
end : ram_access

assign r0data = ram[wr0addr];
assign r1data = ram[r1addr];

endmodule : hs_mem_dpram_asyncrd

