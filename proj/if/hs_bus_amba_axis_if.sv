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
// FILE NAME: hs_bus_amba_axis_if.sv
// AUTHOR:    Onodera Tsusaki
// EMAIL:     apertureelectronic@outlook.com
//-------------------------------------------------------------------------
// RELEASE VERSION: 0.1a0
// VERSION DESCRIPTION: First Edition
//-------------------------------------------------------------------------
// RELEASES:
// VERSION    AUTHOR        RELEASE DATE  DESCRIPTION
// 0.1a0      O. Tsusaki    2025/10/2     First Edition
//-------------------------------------------------------------------------
// PURPOSE: Standard ARM AMBA AXI-Stream interface
//
//-------------------------------------------------------------------------
// PARAMETERS:
// PARAMETER NAME      RANGE       DESCRIPTION                 DEFAULT VALUE
// TDATA_WIDTH         1~16777216  Data width                  8
// TID_WIDTH           0~128       ID width                    1
// TDEST_WIDTH         0~128       Destination width           1
// TUSER_WIDTH         0~16777216  User field width            1
//-FHDR--------------------------------------------------------------------

`include "hs_ifr_global.svh"

`DEFAULT_NETTYPE

// Standard ARM AMBA AXI-Stream interface
interface hs_bus_amba_axis_if
    #(
        parameter int TDATA_WIDTH = 8,
        parameter int TID_WIDTH   = 1,
        parameter int TDEST_WIDTH = 1,
        parameter int TUSER_WIDTH = 1,
        parameter int TKEEP_WIDTH = TDATA_WIDTH / 8,
        parameter int TSTRB_WIDTH = TDATA_WIDTH / 8
    )
    (
        input logic aclk,
        input logic aresetn
    );

    // AXI-4 Stream signals
    logic                   tvalid;
    logic                   tready;
    logic [TDATA_WIDTH-1:0] tdata;
    logic [TSTRB_WIDTH-1:0] tstrb;
    logic [TKEEP_WIDTH-1:0] tkeep;
    logic                   tlast;
    logic [TID_WIDTH-1:0]   tid;
    logic [TDEST_WIDTH-1:0] tdest;
    logic [TUSER_WIDTH-1:0] tuser;
    logic                   twakeup;

    // Master
    modport master
    (
        output tvalid, tdata, tstrb, tkeep, tlast, tid, tdest, tuser, twakeup,
        input  tready
    );

    // Slave
    modport slave
    (
        input  tvalid, tdata, tstrb, tkeep, tlast, tid, tdest, tuser, twakeup,
        output tready
    );

    // Basic assert for interface signals
    //  1. Handshake stable
    property p_hold_payload_until_handshake;
        @(posedge aclk) disable iff (!aresetn)
            tvalid && !tready |-> ##1 (
                $stable(tdata) &&
                $stable(tstrb) &&
                $stable(tkeep) &&
                $stable(tlast) &&
                $stable(tid)   &&
                $stable(tdest) &&
                $stable(tuser) &&
                $stable(twakeup)
            );
    endproperty : p_hold_payload_until_handshake
    assert property (p_hold_payload_until_handshake)
        else $error("AXI-Stream payload changed before handshake");

    //  2. After TVALID = 1, TVALID should not be deasserted until TREADY = 1
    property p_tvalid_hold_until_tready;
        @(posedge aclk) disable iff (!aresetn)
            tvalid && !tready |=> tvalid;
    endproperty : p_tvalid_hold_until_tready
    assert property (p_tvalid_hold_until_tready)
        else $error("AXI-Stream TVALID deasserted before TREADY handshake");

    //  3. Coverage point for handshake
    cover property ( @(posedge aclk) disable iff (!aresetn) tvalid && tready );
endinterface : hs_bus_amba_axis_if
