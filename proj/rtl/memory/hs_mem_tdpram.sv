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
// FILE NAME: hs_mem_tdpram.sv
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
//  True dual-port RAM (2WR) w/ Latency = 1 or 2
//-----------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME    RANGE          DESCRIPTION            DEFAULT VALUE
// DATA_TYPE         type           Item type in RAM       logic[7:0]
// DATA_DEPTH        1 - 1048576    RAM depth              16
// HAS_OUTPUT_DFF    bool_e         Enable/disable output  BOOL_FALSE
//                                  optional DFF
//-FHDR------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// True dual-port RAM (2WR) w/ Latency = 1 or 2
module hs_mem_tdpram
import hs_math_basic_pkg::ceil_to_nxt_pow2;
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter  type   DATA_TYPE     = logic[7:0],
    parameter  int    DATA_DEPTH    = 16,
    parameter  bool_e EN_OUTPUT_REG = BOOL_FALSE,
    `LP_MODULE int    ADDR_WIDTH    = $clog2(DATA_DEPTH)
)
(
    // Clock (the RAM has not reset)
    input  logic                        pa_clk,
    input  logic                        pb_clk,

    // Clock enable
    input  logic                        pa_ce,
    input  logic                        pb_ce,

    // Port A
    input  logic     [ADDR_WIDTH - 1:0] pa_addr,
    input  DATA_TYPE                    pa_wdata,
    input  logic                        pa_wen,
    output DATA_TYPE                    pa_rdata,

    // Port B
    input  logic     [ADDR_WIDTH - 1:0] pb_addr,
    input  DATA_TYPE                    pb_wdata,
    input  logic                        pb_wen,
    output DATA_TYPE                    pb_rdata
);

localparam int DATA_DEPTH_REAL                   = ceil_to_nxt_pow2(DATA_DEPTH);

DATA_TYPE      ram             [DATA_DEPTH_REAL];
DATA_TYPE      pa_ram_rdout;
DATA_TYPE      pb_ram_rdout;

always_ff @(posedge pa_clk) begin : port_a_wr
    if (pa_ce && pa_wen) ram[pa_addr] <= pa_wdata;
end : port_a_wr

always_ff @(posedge pb_clk) begin : port_b_wr
    if (pb_ce && pb_wen) ram[pb_addr] <= pb_wdata;
end : port_b_wr

`GENERATE_START
if (EN_OUTPUT_REG == BOOL_FALSE) begin : no_output_dff
    always_ff @(posedge pa_clk) begin : port_a_rd_ce
        if (pa_ce) begin
            pa_ram_rdout <= ram[pa_addr];
        end
    end : port_a_rd_ce

    always_ff @(posedge pb_clk) begin : port_b_rd_ce
        if (pb_ce) begin
            pb_ram_rdout <= ram[pb_addr];
        end
    end : port_b_rd_ce

    assign pa_rdata = pa_ram_rdout;
    assign pb_rdata = pb_ram_rdout;
end : no_output_dff
else begin : has_output_dff
    always_ff @(posedge pa_clk) begin : port_a_rd_noce
        pa_ram_rdout <= ram[pa_addr];
    end : port_a_rd_noce

    always_ff @(posedge pb_clk) begin : port_b_rd_noce
        pb_ram_rdout <= ram[pb_addr];
    end : port_b_rd_noce

    always_ff @(posedge pa_clk) begin : port_a_odff
        if (pa_ce) pa_rdata <= pa_ram_rdout;
    end : port_a_odff

    always_ff @(posedge pb_clk) begin : port_b_odff
        if (pb_ce) pb_rdata <= pb_ram_rdout;
    end : port_b_odff
end : has_output_dff
`GENERATE_END

endmodule : hs_mem_tdpram

