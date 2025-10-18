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
// FILE NAME: hs_fifo_afifo_sva.sv
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
// PURPOSE: System Verilog Assertion (SVA) mirror for module hs_fifo_afifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE          DESCRIPTION                   DEFAULT VALUE
// DATA_TYPE           type           Type of data in FIFO          logic
// FIFO_DEPTH          2-16777216     Maximum depth of the FIFO     16
// ALMOST_FULL_LVL     0-FIFO_DEPTH   Level to show 'almost full'   FIFO_DEPTH
// ALMOST_EMPTY_LVL    0-FIFO_DEPTH   Level to show 'almost empty'  0
// EN_LAST_SIGNAL      bool_e         If true, user can use 'last'  hs_ifr_misc_typedefs_pkg::BOOL_FALSE
//                                    signals
// EN_PACKET_MODE      bool_e         If true, 'read_valid' will    hs_ifr_misc_typedefs_pkg::BOOL_FALSE
//                                    not be asserted until a full
//                                    packet is available in FIFO
// EN_DROP_PACKET      bool_e         If true, user can use 'wdrop_ hs_ifr_misc_typedefs_pkg::BOOL_FALSE
//                                    packet' port
// EN_PEEK_MODE        bool_e         If true, use can read words
//                                    w/o popping from FIFO by use  hs_ifr_misc_typedefs_pkg::BOOL_FALSE
//                                    the 'rpeek' port
// EN_input_REG       bool_e         Use an extra input register  hs_ifr_misc_typedefs_pkg::BOOL_FALSE
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// System Verilog Assertion (SVA) mirror for module hs_fifo_afifo
module hs_fifo_afifo_sva
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter type   DATA_TYPE        = logic,
    parameter int    FIFO_DEPTH       = 16,
    parameter int    ALMOST_FULL_LVL  = FIFO_DEPTH,
    parameter int    ALMOST_EMPTY_LVL = 0,
    parameter bool_e EN_LAST_SIGNAL   = BOOL_FALSE,
    parameter bool_e EN_PACKET_MODE   = BOOL_FALSE,
    parameter bool_e EN_DROP_PACKET   = BOOL_FALSE,
    parameter bool_e EN_OUTPUT_REG    = BOOL_FALSE,
    `LP_MODULE int   FIFO_LEVEL_WIDTH = $clog2(FIFO_DEPTH + 1)
)
(
    // Clock & reset
    input logic                              src_clk,
    input logic                              src_aresetn,
    input logic                              dst_clk,
    input logic                              dst_aresetn,

    // Write side
    input logic                              wvalid,
    input logic                              wready,
    input DATA_TYPE                          wdata,
    input logic                              wlast,
    input logic                              wdrop,
    input logic                              walmost_full,
    input logic     [FIFO_LEVEL_WIDTH - 1:0] wlevel,

    // Read side
    input logic                              rready,
    input logic                              rvalid,
    input DATA_TYPE                          rdata,
    input logic                              rlast,
    input logic                              ralmost_empty,
    input logic     [FIFO_LEVEL_WIDTH - 1:0] rlevel
);

// X-prop
property wdata_no_x;
    @(posedge src_clk) disable iff (!src_aresetn)
    1 |-> !(wvalid && (wdata === 'x));
endproperty : wdata_no_x
assert property (wdata_no_x) else $error("SVA(%m): Write data has X");

property rdata_no_x;
    @(posedge dst_clk) disable iff (!dst_aresetn)
    1 |-> !(rvalid && (rdata === 'x));
endproperty : rdata_no_x
assert property (rdata_no_x) else $error("SVA(%m): Read data has X");

`GENERATE_START
if (EN_LAST_SIGNAL == BOOL_TRUE) begin
    property p_wlast_defined;
        @(posedge src_clk) disable iff (!src_aresetn)
        wvalid |-> (wlast === 1'b0 || wlast === 1'b1);
    endproperty : p_wlast_defined

    assert property (p_wlast_defined) else $error("SVA(%m): wlast is X when wvalid is high");

    // When enable last signal, rlast should not be 1'bx when rvalid is high
    property p_rlast_defined;
        @(posedge dst_clk) disable iff (!dst_aresetn)
        rvalid |-> (rlast === 1'b0 || rlast === 1'b1);
    endproperty : p_rlast_defined

    assert property (p_rlast_defined) else $error("SVA(%m): rlast is X when rvalid is high");
end
`GENERATE_END

endmodule : hs_fifo_afifo_sva
