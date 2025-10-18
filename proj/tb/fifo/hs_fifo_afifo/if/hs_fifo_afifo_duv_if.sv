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
// FILE NAME: hs_fifo_afifo_duv_if.sv
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
// PURPOSE: Interface for design under verification unit hs_fifo_afifo
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// N/A
//-FHDR--------------------------------------------------------------------
`timescale 1ns/1ps

`include "hs_ifr_global.svh"

`default_nettype `DEFAULT_NETTYPE

// Interface for design under verification unit hs_fifo_afifo
interface hs_fifo_afifo_duv_if
    (
        input logic src_clk,
        input logic src_aresetn,

        input logic dst_clk,
        input logic dst_aresetn
    );
    
    import hs_fifo_afifo_uvm_param_pkg::*;

    localparam int                          FIFO_LEVEL_WIDTH = $clog2(FIFO_DEPTH + 1);

    logic                                   wvalid;
    logic                                   wready;
    DATA_TYPE                               wdata;
    logic                                   wlast;
    logic                                   wdrop;
    logic                                   walmost_full;
    logic          [FIFO_LEVEL_WIDTH - 1:0] wlevel;
    
    logic                                   rready;
    logic                                   rvalid;
    DATA_TYPE                               rdata;
    logic                                   rlast;
    logic                                   ralmost_empty;
    logic          [FIFO_LEVEL_WIDTH - 1:0] rlevel;
    

    // Clocking
    clocking cb_wr @(posedge src_clk);
        default input #1step output #1step;

        input  wready;
        input  walmost_full;

        output wvalid;
        output wdata;
        output wlast;
        output wdrop;

        input  wlevel;
    endclocking : cb_wr
    

    clocking cb_wr_mon @(posedge src_clk);
        default input #1step output #1step;

        input wready;
        input walmost_full;

        input wvalid_i = wvalid;
        input wdata_i  = wdata;
        input wlast_i  = wlast;
        input wdrop_i  = wdrop;

        input wlevel;
    endclocking : cb_wr_mon

    clocking cb_rd @(posedge dst_clk);
        default input #1step output #1step;
        input  rvalid;
        input  rdata;
        input  rlast;

        output rready;

        input  rlevel;
    endclocking : cb_rd

    clocking cb_rd_mon @(posedge dst_clk);
        default input #1step output #1step;
        input  rvalid;
        input  rdata;
        input  rlast;

        input  rready_i = rready;

        input  rlevel;
    endclocking : cb_rd_mon

    // Write side
    modport wr(clocking cb_wr, clocking cb_wr_mon, input src_aresetn);

    // Read side
    modport rd(clocking cb_rd, clocking cb_rd_mon, input dst_aresetn);
    
    // Assertions for holding after handshake required
    property p_wr_hold;
        @(posedge src_clk) disable iff (!src_aresetn)
            wvalid && !wready |=> $stable(wdata) && $stable(wlast);
    endproperty : p_wr_hold
    a_wr_hold: assert property (p_wr_hold);

    property p_rd_hold;
        @(posedge dst_clk) disable iff (!dst_aresetn)
            rvalid && !rready |=> $stable(rdata) && $stable(rlast);
    endproperty : p_rd_hold
    a_rd_hold: assert property (p_rd_hold);
endinterface : hs_fifo_afifo_duv_if