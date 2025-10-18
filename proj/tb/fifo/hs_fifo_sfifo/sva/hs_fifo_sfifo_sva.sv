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
// FILE NAME: hs_fifo_sfifo_sva.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/9/19     First Edition
//-------------------------------------------------------------------------
// PURPOSE: System Verilog Assertion (SVA) mirror for module hs_fifo_sfifo
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

// System Verilog Assertion (SVA) mirror for module hs_fifo_sfifo
module hs_fifo_sfifo_sva
import hs_ifr_misc_typedefs_pkg::*;
#(
    parameter type   DATA_TYPE        = logic,
    parameter int    FIFO_DEPTH       = 16,
    parameter int    ALMOST_FULL_LVL  = FIFO_DEPTH,
    parameter int    ALMOST_EMPTY_LVL = 0,
    parameter bool_e EN_LAST_SIGNAL   = BOOL_FALSE,
    parameter bool_e EN_PACKET_MODE   = BOOL_FALSE,
    parameter bool_e EN_DROP_PACKET   = BOOL_FALSE,
    parameter bool_e EN_PEEK_MODE     = BOOL_FALSE,
    parameter bool_e EN_OUTPUT_REG    = BOOL_FALSE,
    `LP_MODULE int   FIFO_LEVEL_WIDTH = $clog2(FIFO_DEPTH + 1)
)
(
    // Clock & reset
    input logic                              clk,
    input logic                              aresetn,      // Note: The reset only reset control logic

    // Write side
    input logic                              wvalid,
    input logic                              wready,
    input DATA_TYPE                          wdata,
    input logic                              wlast,
    input logic                              wdrop,
    input logic                              walmost_full,

    // Read side
    input logic                              rready,
    input logic                              rvalid,
    input DATA_TYPE                          rdata,
    input logic                              rlast,
    input logic                              rpeek,
    input logic                              ralmost_empty,

    // Internal signals
    input logic     [FIFO_LEVEL_WIDTH - 1:0] level
);

localparam int REAL_FIFO_DEPTH    = (EN_OUTPUT_REG == BOOL_TRUE) ? (FIFO_DEPTH + 1) : FIFO_DEPTH;

default clocking cb @(posedge clk);
endclocking : cb
default disable iff (!aresetn);

int            level_q;
int            packet_level;

int            packet_length;
int            dropped_length;

logic          write_accept;
logic          read_accept;

assign write_accept = wready && wvalid;
assign read_accept  = rready && rvalid;

always_ff @(posedge clk, negedge aresetn) begin
    if (!aresetn) begin
        packet_length      <= 0;
    end
    else if (write_accept) begin
        if (wlast || wdrop) begin
            packet_length      <= 0;
        end
        else begin
            packet_length      <= packet_length + 1;
        end
    end
end

assign dropped_length = packet_length + (write_accept ? 1 : 0);

always_ff @(posedge clk, negedge aresetn) begin
    if (!aresetn) begin
        level_q <= 0;
    end
    else begin
        level_q <= level_q -
        (wdrop ? dropped_length : 0) +
        (write_accept ? 1 : 0) -
        ((read_accept && !rpeek) ? 1 : 0);
    end
end

always_ff @(posedge clk, negedge aresetn) begin : packet_level_stat
    if (!aresetn) begin
        packet_level <= 0;
    end
    else begin
        packet_level <= packet_level +
        ((write_accept && wlast && !wdrop) ? 1 : 0) -
        ((read_accept && rlast && !rpeek) ? 1 : 0);
    end
end : packet_level_stat

// Sequence definitions
sequence s_both_wr_rd;
    (write_accept) && (read_accept);
endsequence : s_both_wr_rd

sequence write_to_full;
    ((level_q == (REAL_FIFO_DEPTH - 1)) && write_accept && !read_accept);
endsequence : write_to_full

// Standard FIFO flags (FULL/EMPTY/ALMOST_FULL/ALMOST_EMPTY)
property p_full_flag;
    write_to_full |-> (wready == 1);
endproperty : p_full_flag
assert property (p_full_flag)        else $error("SVA(%m): Full flag incorrect");

// property p_full_throttle_one_cycle;
//     write_to_full |=> (!wready);
// endproperty : p_full_throttle_one_cycle
// assert property (p_full_throttle_one_cycle) else $error("SVA(%m): Full flag throttle incorrect");

`GENERATE_START
if (EN_PACKET_MODE == BOOL_FALSE) begin
    if (EN_OUTPUT_REG == BOOL_FALSE) begin
        property p_empty_flag;
            level_q == 0 |-> rvalid == 0;
        endproperty : p_empty_flag
        assert property (p_empty_flag)       else $error("SVA(%m): Empty flag incorrect");
    end
    else begin
        property p_empty_flag;
            level_q == 0 |=> rvalid == 0;
        endproperty : p_empty_flag
        assert property (p_empty_flag)       else $error("SVA(%m): Empty flag incorrect");
    end
end
else begin
    property p_empty_flag;
        (level_q == 0) || (packet_level == 0) |-> rvalid == 0;
    endproperty : p_empty_flag
    assert property (p_empty_flag)       else $error("SVA(%m): Empty flag incorrect");
end
`GENERATE_END

`GENERATE_START
if (ALMOST_FULL_LVL == FIFO_DEPTH) begin

    property p_almost_full_flag;
        walmost_full == !wready;
    endproperty : p_almost_full_flag
    assert property (p_almost_full_flag)  else $error("SVA(%m): Almost Full flag incorrect");

end
else begin

    property p_almost_full_flag;
        level_q |=> walmost_full == (level_q >= ALMOST_FULL_LVL);
    endproperty : p_almost_full_flag
    assert property (p_almost_full_flag)  else $error("SVA(%m): Almost Full flag incorrect");

end
`GENERATE_END

`GENERATE_START
if (ALMOST_EMPTY_LVL == 0) begin

    property p_almost_empty_flag;
        ralmost_empty == !rvalid;
    endproperty : p_almost_empty_flag
    assert property (p_almost_empty_flag) else $error("SVA(%m): Almost Empty flag incorrect");

end
else begin

    property p_almost_empty_flag;
        level_q |=> ralmost_empty == (level_q <= ALMOST_EMPTY_LVL);
    endproperty : p_almost_empty_flag
    assert property (p_almost_empty_flag) else $error("SVA(%m): Almost Empty flag incorrect");

end
`GENERATE_END

// When FIFO full/empty, wready/rvalid should not change until a read/write occurs
property p_no_overflow;
    !(write_accept && (level_q == REAL_FIFO_DEPTH));
endproperty : p_no_overflow

property p_no_underflow;
    !(read_accept && (level_q == 0));
endproperty : p_no_underflow

assert property (p_no_overflow)  else $error("SVA(%m): FIFO Overflow");
assert property (p_no_underflow) else $error("SVA(%m): FIFO Underflow");

// X-prop
property data_no_x;
    1 |-> !(wvalid && (wdata === 'x)) && !(rvalid && (rdata === 'x));
endproperty : data_no_x
assert property (data_no_x) else $error("SVA(%m): Data has X");

`GENERATE_START
if (EN_LAST_SIGNAL == BOOL_TRUE) begin
    // When enable last signal, rlast should not be 1'bx when rvalid is high
    property p_rlast_defined;
        rvalid |-> (rlast === 1'b0 || rlast === 1'b1);
    endproperty : p_rlast_defined

    assert property (p_rlast_defined) else $error("SVA(%m): rlast is X when rvalid is high");
end
`GENERATE_END

endmodule : hs_fifo_sfifo_sva
